//! Section 7 of RECIPE.md: the cell sums.
//!
//! For a gap tuple g, the sum `S_g` runs over all n^(k+1) height tuples a, and its term
//! cost(g, a) is the cost of the cheapest path from point 0 to point k through the interior
//! points 1, …, k − 1, where the edge between the points i and j costs `E_ij`.
//!
//! Let f(S, j), for a non-empty set S of interior points and a point j of S, be the cost of the
//! cheapest path that starts at point 0, visits the points of S and no others, and ends at j.
//! A path is a shorter path and one more edge, so
//!
//! ```text
//! f({j}, j) = E_0j,
//! f(S, j)   = min over i in S∖{j} of  f(S∖{j}, i) + E_ij,
//! cost      = min over j of  f({1, …, k − 1}, j) + E_jk.
//! ```
//!
//! The value f(S, j) depends only on the heights of point 0 and of the points of S. The heights
//! are therefore fixed one point at a time, in the order 0, 1, …, k. When the height of the
//! interior point l has been fixed, the values f(S, j) for the sets S with largest element l
//! are computed; they serve all height tuples that begin with the same heights of the points
//! 0, …, l. The height of point k enters the last line only.
//!
//! This sharing is the only saving. No symmetry is used: every one of the m^k gap tuples and
//! every one of the n^(k+1) height tuples is gone through.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use crate::arith::{length, mul, narrow, power, raise, wide};
use crate::failure::{invalid, note, Outcome, Stop};
use crate::files::Params;
use crate::keys::{Keys, MAX_CELLS};
use crate::sizes::Sizes;

/// The largest number of gaps in a block that a spec file may ask for.
pub const MAX_GAPS: usize = 8;
/// The largest number of height cells that a spec file may ask for.
pub const MAX_HEIGHTS: usize = 16;

/// Points of a block.
const POINTS: usize = MAX_GAPS + 1;
/// Interior points of a block.
const INNER: usize = MAX_GAPS - 1;
/// Places per set in the table of f, one for each end j; a power of two.
const ENDS: usize = 8;
/// The length of the table of f.
const STATES: usize = (1 << INNER) * ENDS;
/// `E_ij` with i < j is kept at the place i·`STRIDE` + j.
const STRIDE: usize = 16;
/// The length of the table of edge costs.
const EDGES: usize = 256;

const _: () = assert!(ENDS >= INNER && STRIDE >= POINTS && EDGES >= POINTS * STRIDE);
const _: () = assert!(STATES <= 1 << 16 && STATES.is_power_of_two() && EDGES.is_power_of_two());

/// The interior point `point` as an element of a set: the sets are bit masks.
fn bit(point: usize) -> usize {
    1 << (point - 1)
}

/// The place of f(S, j) in the table of f.
fn place(set: usize, end: usize) -> usize {
    set * ENDS + (end - 1)
}

/// The place of `E_ij` in the table of edge costs.
fn edge(i: usize, j: usize) -> usize {
    i.min(j) * STRIDE + i.max(j)
}

/// A place in one of the two tables, in 16 bits to keep the plan small.
fn short(place: usize) -> u16 {
    u16::try_from(place).expect("the tables have at most 2^16 places")
}

/// One term f(S∖{j}, i) + `E_ij` of a minimum, by the places of its two parts.
#[derive(Clone, Copy)]
struct Term {
    state: u16,
    edge: u16,
}

/// The values f(S, j) for sets S of one size s ≥ 2: each is a minimum of s − 1 terms.
struct Round {
    /// s − 1.
    terms: usize,
    /// The places of the values f(S, j).
    targets: Vec<u16>,
    /// The terms of all the minima, `terms` for each target.
    sources: Vec<Term>,
}

/// What is computed when the height of the interior point l is fixed: f(S, j) for every set S
/// with largest element l, the smaller sets first.
struct Level {
    /// f({l}, l) = `E_0l`.
    first: Term,
    rounds: Vec<Round>,
}

impl Level {
    fn new(point: usize) -> Self {
        let members = |set: usize| (1..=point).filter(move |&p| set & bit(p) != 0);
        let top = bit(point);
        let mut rounds: Vec<Round> = (1..point)
            .map(|terms| Round {
                terms,
                targets: Vec::new(),
                sources: Vec::new(),
            })
            .collect();
        // The sets with largest element l, other than {l} itself.
        for set in top + 1..2 * top {
            let round = &mut rounds[members(set).count() - 2];
            for end in members(set) {
                // S∖{j} is a set of an earlier level if j = l; otherwise it contains l and is
                // one element smaller than S, so it is {l} or belongs to the round before.
                let before = set ^ bit(end);
                round.targets.push(short(place(set, end)));
                round.sources.extend(members(before).map(|via| Term {
                    state: short(place(before, via)),
                    edge: short(edge(via, end)),
                }));
            }
        }
        Self {
            first: Term {
                state: short(place(top, point)),
                edge: short(edge(0, point)),
            },
            rounds,
        }
    }

    /// Computes the values of this level.
    fn apply(&self, states: &mut [u64; STATES], edges: &[u64; EDGES]) {
        states[usize::from(self.first.state) % STATES] =
            edges[usize::from(self.first.edge) % EDGES];
        for round in &self.rounds {
            match round.terms {
                1 => round.apply::<1>(states, edges),
                2 => round.apply::<2>(states, edges),
                3 => round.apply::<3>(states, edges),
                4 => round.apply::<4>(states, edges),
                5 => round.apply::<5>(states, edges),
                6 => round.apply::<6>(states, edges),
                terms => {
                    let minima = round.sources.chunks_exact(terms);
                    for (&target, terms) in round.targets.iter().zip(minima) {
                        states[usize::from(target) % STATES] = least(terms, states, edges);
                    }
                }
            }
        }
    }
}

impl Round {
    /// Computes the minima of this round. `TERMS` must be `self.terms`; the compiler, knowing
    /// the number of terms, can then write out the loop over them.
    fn apply<const TERMS: usize>(&self, states: &mut [u64; STATES], edges: &[u64; EDGES]) {
        let (minima, _) = self.sources.as_chunks::<TERMS>();
        for (&target, terms) in self.targets.iter().zip(minima) {
            states[usize::from(target) % STATES] = least(terms, states, edges);
        }
    }
}

/// The least of the given terms f(S∖{j}, i) + `E_ij`.
///
/// No sum can overflow: see `cell_sums`. Reducing a place modulo the length of its table
/// changes nothing, since the places of a plan lie inside the tables; it shows this to the
/// compiler.
#[inline]
fn least(terms: &[Term], states: &[u64; STATES], edges: &[u64; EDGES]) -> u64 {
    let mut best = u64::MAX;
    for term in terms {
        let state = states[usize::from(term.state) % STATES];
        best = best.min(state + edges[usize::from(term.edge) % EDGES]);
    }
    best
}

/// The order of the computation for blocks of k gaps; it depends on k alone.
struct Plan {
    /// The levels of the interior points 1, …, k − 1.
    levels: Vec<Level>,
    /// The places of f({1, …, k − 1}, j) for j = 1, …, k − 1.
    ends: Vec<u16>,
}

impl Plan {
    fn new(k: usize) -> Self {
        let inner = k - 1;
        let all = (1 << inner) - 1;
        Self {
            levels: (1..=inner).map(Level::new).collect(),
            ends: (1..=inner).map(|end| short(place(all, end))).collect(),
        }
    }
}

/// The working tables of one thread.
struct Walker<'a> {
    plan: &'a Plan,
    keys: &'a Keys,
    /// Tab by rows, as in `Tables`.
    table: &'a [u64],
    /// m, the number of gap cells.
    cells: usize,
    /// k, the number of gaps in a block.
    k: usize,
    /// n, the number of height cells.
    n: usize,
    /// For i < j, the row Tab(κ(i, j), ·) of the current gap tuple.
    rows: [[&'a [u64]; POINTS]; POINTS],
    /// For an interior point j, `E_jk` as a function of the heights of j and k.
    last: [[[u64; MAX_HEIGHTS]; MAX_HEIGHTS]; INNER],
    /// The heights fixed so far.
    heights: [usize; POINTS],
    /// The edge costs between the points whose heights are fixed.
    edges: [u64; EDGES],
    /// The table of f.
    states: [u64; STATES],
    /// The sum of the costs so far.
    sum: u128,
}

impl<'a> Walker<'a> {
    fn new(plan: &'a Plan, keys: &'a Keys, table: &'a [u64], params: &Params) -> Self {
        Self {
            plan,
            keys,
            table,
            cells: params.cells(),
            k: params.k,
            n: params.n,
            rows: [[&[]; POINTS]; POINTS],
            last: [[[0; MAX_HEIGHTS]; MAX_HEIGHTS]; INNER],
            heights: [0; POINTS],
            edges: [0; EDGES],
            states: [0; STATES],
            sum: 0,
        }
    }

    /// `S_g` for the gap tuple with the given index.
    fn cell_sum(&mut self, index: usize) -> Outcome<u128> {
        let (k, n) = (self.k, self.n);
        // g_1, …, g_k are the digits of the index in base m, the lowest first.
        let mut gaps = [0; MAX_GAPS];
        let mut rest = index;
        for gap in &mut gaps[..k] {
            *gap = rest % self.cells;
            rest /= self.cells;
        }
        // κ(i, j) counts the entries of (g_{i+1}, …, g_j) by cell.
        for i in 0..k {
            let mut key = [0; MAX_CELLS];
            for j in i + 1..=k {
                key[gaps[j - 1]] += 1;
                let Some(rank) = self.keys.rank(key) else {
                    return invalid("internal error: a key is missing".to_string());
                };
                self.rows[i][j] = &self.table[rank * n..][..n];
            }
        }
        for j in 1..k {
            for (a, row) in self.last[j - 1].iter_mut().enumerate().take(n) {
                for (b, cost) in row.iter_mut().enumerate().take(n) {
                    *cost = self.rows[j][k][a.abs_diff(b)];
                }
            }
        }
        self.sum = 0;
        self.descend(0);
        Ok(self.sum)
    }

    /// Runs through the heights of the points `point`, …, k, the heights before being fixed.
    fn descend(&mut self, point: usize) {
        let plan = self.plan;
        for height in 0..self.n {
            self.heights[point] = height;
            if point > 0 {
                for earlier in 0..point {
                    let difference = height.abs_diff(self.heights[earlier]);
                    self.edges[edge(earlier, point)] = self.rows[earlier][point][difference];
                }
                plan.levels[point - 1].apply(&mut self.states, &self.edges);
            }
            if point < plan.levels.len() {
                self.descend(point + 1);
            } else {
                self.finish();
            }
        }
    }

    /// Adds cost(g, a) for the n heights of point k, the other heights being fixed.
    fn finish(&mut self) {
        let n = self.n;
        let mut best = [u64::MAX; MAX_HEIGHTS];
        for (j, &end) in self.plan.ends.iter().enumerate() {
            let state = self.states[usize::from(end) % STATES];
            let costs = &self.last[j][self.heights[j + 1]];
            for (best, &cost) in best[..n].iter_mut().zip(&costs[..n]) {
                *best = (*best).min(state + cost);
            }
        }
        let costs: u64 = best[..n].iter().sum();
        self.sum += u128::from(costs);
    }
}

/// Reports on the standard error stream how far the cell sums have come.
struct Progress {
    started: Instant,
    count: usize,
    finished: AtomicUsize,
}

impl Progress {
    /// Counts one more cell sum and says so at every tenth of the way, unless the work is short.
    fn step(&self) {
        let finished = self.finished.fetch_add(1, Ordering::Relaxed) + 1;
        let tenths = finished * 10 / self.count;
        let elapsed = self.started.elapsed();
        if tenths != (finished - 1) * 10 / self.count && elapsed >= Duration::from_secs(2) {
            note(&format!(
                "rchk: {finished} of {} cell sums after {} s",
                self.count,
                elapsed.as_secs()
            ));
        }
    }
}

/// The cell sums `S_g` of all m^k gap tuples in index order, computed by at most `threads`
/// threads.
pub fn cell_sums(
    params: &Params,
    keys: &Keys,
    table: &[u64],
    threads: usize,
    sizes: &mut Sizes,
) -> Outcome<Vec<u128>> {
    // A path has at most k edges, so every value f(S, j) and every cost is at most k times the
    // largest entry of Tab. If n times this bound fits in 64 bits, then no sum of an edge cost
    // and a value of f, and no sum of the costs for the n heights of point k, can overflow.
    let largest = u128::from(table.iter().copied().max().unwrap_or(0));
    let bound = mul(wide(params.k), largest, "the bound for cost(g, a)")?;
    narrow(mul(bound, wide(params.n), "n·cost")?, "n·cost")?;
    raise(&mut sizes.cost, bound);
    let tuples = power(wide(params.n), params.k + 1, "n^(k+1)")?;
    let all = mul(bound, tuples, "k·max(Tab)·n^(k+1)")?;
    raise(&mut sizes.cell_sum_bound, all);

    let count = power(wide(params.cells()), params.k, "m^k")?;
    let count = length(count, "the number of gap tuples")?;
    let plan = Plan::new(params.k);
    let next = AtomicUsize::new(0);
    let progress = Progress {
        started: Instant::now(),
        count,
        finished: AtomicUsize::new(0),
    };
    // Each thread takes the next index that no thread has taken, until none is left. A sum
    // depends on its index alone, so the result does not depend on the number of threads.
    let work = || -> Outcome<Vec<(usize, u128)>> {
        let mut walker = Box::new(Walker::new(&plan, keys, table, params));
        let mut found = Vec::new();
        loop {
            let index = next.fetch_add(1, Ordering::Relaxed);
            if index >= count {
                return Ok(found);
            }
            found.push((index, walker.cell_sum(index)?));
            progress.step();
        }
    };
    let parts: Vec<Outcome<Vec<(usize, u128)>>> = thread::scope(|scope| {
        // More threads than gap tuples would find nothing to do.
        let handles: Vec<_> = (0..threads.min(count)).map(|_| scope.spawn(work)).collect();
        let stopped = || invalid("internal error: a thread stopped".to_string());
        handles
            .into_iter()
            .map(|handle| handle.join().unwrap_or_else(|_| stopped()))
            .collect()
    });

    let mut sums = vec![None; count];
    for part in parts {
        for (index, sum) in part? {
            sums[index] = Some(sum);
            raise(&mut sizes.cell_sum, sum);
        }
    }
    let missing = || Stop::Invalid("internal error: a cell sum is missing".to_string());
    sums.into_iter()
        .map(|sum| sum.ok_or_else(missing))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith::tests::Random;

    fn params(k: usize, cells: usize, n: usize) -> Params {
        Params {
            k,
            h1: 2,
            h2: 1,
            mesh: 2,
            boundaries: (1..cells).map(|b| u64::try_from(b).unwrap()).collect(),
            n,
            nu: 1,
            tail: 1,
        }
    }

    /// A table with entries below 2^38 that have nothing to do with distances.
    fn random_table(keys: &Keys, n: usize, random: &mut Random) -> Vec<u64> {
        (0..keys.len() * n).map(|_| random.below(1 << 38)).collect()
    }

    /// The cheapest way from `at` through the interior points not yet visited to point k, found
    /// by trying every order.
    fn cheapest(e: &[[u64; POINTS]; POINTS], k: usize, at: usize, visited: usize) -> u64 {
        if visited == (1 << (k - 1)) - 1 {
            return e[at][k];
        }
        (1..k)
            .filter(|&next| visited & bit(next) == 0)
            .map(|next| e[at][next] + cheapest(e, k, next, visited | bit(next)))
            .min()
            .unwrap()
    }

    /// `S_g` straight from the definitions of Section 7.
    fn sum_by_search(params: &Params, keys: &Keys, table: &[u64], index: usize) -> u128 {
        let (k, n, m) = (params.k, params.n, params.cells());
        let g = |i: usize| index / m.pow(u32::try_from(i - 1).unwrap()) % m;
        let mut sum = 0;
        for tuple in 0..n.pow(u32::try_from(k + 1).unwrap()) {
            let a = |i: usize| tuple / n.pow(u32::try_from(i).unwrap()) % n;
            let mut e = [[0; POINTS]; POINTS];
            for i in 0..k {
                for j in i + 1..=k {
                    let mut key = [0; MAX_CELLS];
                    for between in i + 1..=j {
                        key[g(between)] += 1;
                    }
                    let rank = keys.rank(key).unwrap();
                    e[i][j] = table[rank * n + a(i).abs_diff(a(j))];
                    e[j][i] = e[i][j];
                }
            }
            sum += u128::from(cheapest(&e, k, 0, 0));
        }
        sum
    }

    #[test]
    fn the_plan_has_every_value_once() {
        for k in 2..=MAX_GAPS {
            let inner = k - 1;
            let plan = Plan::new(k);
            let mut targets = Vec::new();
            let mut terms = 0;
            for level in &plan.levels {
                targets.push(level.first.state);
                for round in &level.rounds {
                    assert_eq!(round.sources.len(), round.terms * round.targets.len());
                    // Every term uses a value that has been computed before.
                    for (target, sources) in
                        round.targets.iter().zip(round.sources.chunks(round.terms))
                    {
                        assert!(sources.iter().all(|term| targets.contains(&term.state)));
                        targets.push(*target);
                    }
                    terms += round.sources.len();
                }
            }
            // There are j·C(k − 1, j) pairs (S, j) with |S| = j, hence (k − 1)·2^(k − 2) values,
            // and each value with |S| ≥ 2 is a minimum of |S| − 1 terms.
            assert_eq!(targets.len(), inner << (inner - 1));
            let mut distinct = targets.clone();
            distinct.sort_unstable();
            distinct.dedup();
            assert_eq!(distinct.len(), targets.len());
            if inner >= 2 {
                assert_eq!(terms, (inner * (inner - 1)) << (inner - 2));
            }
            assert!(plan.ends.iter().all(|end| targets.contains(end)));
        }
    }

    #[test]
    fn cell_sums_agree_with_a_search_over_all_orders() {
        let mut random = Random(4);
        let cases = [
            (2, 1, 1),
            (2, 1, 5),
            (2, 3, 4),
            (3, 2, 5),
            (3, 3, 3),
            (4, 2, 3),
            (4, 4, 3),
            (5, 3, 2),
            (5, 5, 2),
            (6, 2, 2),
            (6, 6, 2),
            (7, 3, 2),
            (7, 7, 1),
            (8, 2, 2),
            (8, 8, 1),
        ];
        for (k, cells, n) in cases {
            let params = params(k, cells, n);
            let keys = Keys::new(cells, u8::try_from(k).unwrap());
            let table = random_table(&keys, n, &mut random);
            let plan = Plan::new(k);
            let mut walker = Walker::new(&plan, &keys, &table, &params);
            let count = cells.pow(u32::try_from(k).unwrap());
            let bound = u64::try_from(count).unwrap();
            let mut indices: Vec<usize> = (0..4)
                .map(|_| usize::try_from(random.below(bound)).unwrap())
                .collect();
            indices.extend([0, count - 1]);
            if cells >= k {
                // g = (0, 1, …, k − 1): all the keys κ(i, j) are different, so that the edge
                // costs are independent random numbers.
                indices.push(
                    (0..k)
                        .map(|i| i * cells.pow(u32::try_from(i).unwrap()))
                        .sum(),
                );
            }
            for index in indices {
                assert_eq!(
                    walker.cell_sum(index).unwrap(),
                    sum_by_search(&params, &keys, &table, index),
                    "k = {k}, m = {cells}, n = {n}, index {index}"
                );
            }
        }
    }

    #[test]
    fn the_number_of_threads_does_not_matter() {
        let mut random = Random(5);
        let params = params(4, 3, 3);
        let keys = Keys::new(3, 4);
        let table = random_table(&keys, 3, &mut random);
        let mut sizes = Sizes::default();
        let single = cell_sums(&params, &keys, &table, 1, &mut sizes).unwrap();
        assert_eq!(single.len(), 81);
        for (index, &sum) in single.iter().enumerate() {
            assert_eq!(sum, sum_by_search(&params, &keys, &table, index));
        }
        for threads in [2, 3, 4] {
            assert_eq!(
                cell_sums(&params, &keys, &table, threads, &mut sizes).unwrap(),
                single
            );
        }
        assert_eq!(sizes.cell_sum, *single.iter().max().unwrap());
        // Reversing a gap tuple reverses the block, which does not change the sum.
        let reversed = |index: usize| {
            (0..4)
                .fold((0, index), |(r, i), _| (r * 3 + i % 3, i / 3))
                .0
        };
        assert!((0..81).all(|index| single[index] == single[reversed(index)]));
    }

    #[test]
    fn a_table_that_is_too_large_is_refused() {
        let params = params(2, 1, 2);
        let keys = Keys::new(1, 2);
        let mut sizes = Sizes::default();
        let table = vec![u64::MAX / 4; keys.len() * 2];
        assert!(cell_sums(&params, &keys, &table, 1, &mut sizes).is_ok());
        let table = vec![u64::MAX / 4 + 1; keys.len() * 2];
        assert!(cell_sums(&params, &keys, &table, 1, &mut sizes).is_err());
    }

    /// Not a test: the time for a height tuple with k = 7 and n = 6 on a table of random
    /// numbers. Run it with `cargo test --release -- --ignored --nocapture timing`.
    #[test]
    #[ignore = "a measurement, not a test"]
    fn timing_for_seven_gaps() {
        let mut random = Random(6);
        let params = params(7, 4, 6);
        let keys = Keys::new(4, 7);
        let table = random_table(&keys, 6, &mut random);
        let plan = Plan::new(7);
        let mut walker = Walker::new(&plan, &keys, &table, &params);
        let tuples = 6_u128.pow(8);
        let (mut best, mut all) = (u128::MAX, 0);
        for index in 0..12 {
            let started = Instant::now();
            walker.cell_sum(index * 1000 + 7).unwrap();
            let time = started.elapsed().as_nanos() * 1000 / tuples;
            best = best.min(time);
            all += time;
        }
        let mean = all / 12;
        println!(
            "12 cell sums: {}.{:03} ns for a height tuple on average, {}.{:03} ns at best",
            mean / 1000,
            mean % 1000,
            best / 1000,
            best % 1000
        );
    }
}
