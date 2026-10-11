//! Section 7 of RECIPE.md: the cell sums.
//!
//! For a gap tuple g, the sum `S_g` runs over all n^(k+1) height tuples a, and its term
//! cost(g, a) is the cost of the cheapest path from point 0 to point k through the interior
//! points 1, …, k − 1, where the edge between the points i and j costs `E_ij`.
//!
//! # The paths between interior points
//!
//! A path from point 0 to point k through the interior points is an edge from 0 to an interior
//! point i, a path from i through all the interior points to an interior point j, and an edge
//! from j to k. Let P(i, j) be the cost of the cheapest path from i to j through all the
//! interior points; the recipe writes H(u, v). Then
//!
//! ```text
//! cost(g, a) = min over i ≠ j of  E_0i + P(i, j) + E_jk      for k ≥ 3,
//! cost(g, a) = E_01 + E_12                                   for k = 2,
//! ```
//!
//! where k = 2 has the single interior point 1 and no path between interior points.
//!
//! By the identity *Shared paths* of Section 7, P(i, j) depends only on the *inner tuple*
//! (g_2, …, g_{k−1}) and on the interior heights a_1, …, a_{k−1}. The work is therefore done
//! inner tuple by inner tuple: for every choice of the interior heights, P is computed once
//! and serves the m² gap tuples (g_1, g_2, …, g_{k−1}, g_k) and the n² heights (a_0, a_k).
//!
//! # How P is computed
//!
//! Let f(S, j), for a non-empty set S of interior points other than point 1 and a point j of S,
//! be the cost of the cheapest path that starts at point 1, visits the points of S and no
//! others, and ends at j. A path is a shorter path and one more edge, so
//!
//! ```text
//! f({j}, j) = E_1j,
//! f(S, j)   = min over i in S∖{j} of  f(S∖{j}, i) + E_ij.
//! ```
//!
//! Let A = {2, …, k − 1}. A path from point 1 through all the interior points to j costs at
//! least f(A, j), and one of them costs that; read backwards it is a path from j to 1 with the
//! same cost, because `E_ij` = `E_ji`. A path from i to j through all the interior points, where
//! i and j are both different from point 1, passes point 1; the part before point 1, read
//! backwards, is a path from 1 through a set S that contains i and ends at i, and the part
//! after it is a path from 1 through A∖S, which contains j, and ends at j. Conversely two such
//! paths, joined at point 1, make a path from i to j through all the interior points. So
//!
//! ```text
//! P(1, j) = P(j, 1) = f(A, j),
//! P(i, j) = P(j, i) = min over S with i in S, j not in S of  f(S, i) + f(A∖S, j).
//! ```
//!
//! The value f(S, j) depends only on the heights of point 1 and of the points of S. The interior
//! heights are therefore fixed one point at a time, in the order 1, 2, …, k − 1. When the
//! height of the point l ≥ 2 has been fixed, the values f(S, j) for the sets S with largest
//! element l are computed; they serve all height tuples that have the same heights of the
//! points 1, …, l.
//!
//! # The two ends
//!
//! When all interior heights are fixed, P is known, and for every g_1 and a_0
//!
//! ```text
//! reach(j) = min over i ≠ j of  E_0i + P(i, j)      (k = 2: reach(1) = E_01)
//! ```
//!
//! is the cost of the cheapest path from point 0 through all the interior points to j. Then,
//! for every g_k and a_k as well, cost(g, a) = min over j of reach(j) + `E_jk`.
//!
//! # The three identities
//!
//! The three identities of Section 7 are used so that fewer terms are formed; every sum that is
//! returned is the number defined there. *Shared paths* is the scheme above. *Reflection*: only
//! the heights y ≤ n − 1 − y of point 1 are gone through, and the contribution of a height
//! y < n − 1 − y is counted twice (`Walker::block`). *Reversal*: of an inner tuple and the one
//! read backwards only one is computed, and each of its sums is stored for both gap tuples
//! (`cell_sums`).
//!
//! # Arithmetic
//!
//! Costs of paths are kept in 64 bits and cell sums in 128 bits. `cell_sums` checks two bounds
//! before anything is computed and says there why they exclude overflow. The release profile
//! also sets `overflow-checks`, so that an addition or a multiplication in this file that did
//! not fit would stop the program with status 2.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use crate::arith::{length, mul, narrow, power, raise, wide};
use crate::failure::{invalid, note, Outcome, Stop};
use crate::files::Params;
use crate::keys::{Key, Keys, MAX_CELLS};
use crate::sizes::Sizes;

/// The largest number of gaps in a block that a spec file may ask for.
pub const MAX_GAPS: usize = 9;
/// The largest number of height cells that a spec file may ask for.
pub const MAX_HEIGHTS: usize = 16;

/// Points of a block.
const POINTS: usize = MAX_GAPS + 1;
/// Interior points of a block.
const INTERIOR: usize = MAX_GAPS - 1;
/// Interior points other than point 1: the sets S of f(S, j) consist of these.
const OTHERS: usize = MAX_GAPS - 2;
/// Places per set in the table of f, one for each end j; a power of two.
const ENDS: usize = 8;
/// The length of the table of f.
const STATES: usize = (1 << OTHERS) * ENDS;
/// `E_ij` with i < j is kept at the place i·`STRIDE` + j.
const STRIDE: usize = 16;
/// The length of the table of edge costs.
const EDGES: usize = 256;

// The tables have a place for every end of every set and for every edge of a block of `MAX_GAPS`
// gaps, and a place fits in the 16 bits in which the plan keeps it.
const _: () = assert!(ENDS >= OTHERS && STRIDE >= POINTS && EDGES >= POINTS * STRIDE);
const _: () = assert!(STATES <= 1 << 16 && STATES.is_power_of_two() && EDGES.is_power_of_two());
// `Walker::descend` has a case for each number of interior points from 1 to 8.
const _: () = assert!(INTERIOR <= 8);

/// The point `point` ≥ 2 as an element of a set: the sets are bit masks.
fn bit(point: usize) -> usize {
    1 << (point - 2)
}

/// The place of f(S, j) in the table of f.
fn place(set: usize, end: usize) -> usize {
    set * ENDS + (end - 2)
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

/// What is computed when the height of the point l ≥ 2 is fixed: f(S, j) for every set S with
/// largest element l, the smaller sets first.
struct Level {
    /// f({l}, l) = `E_1l`.
    first: Term,
    rounds: Vec<Round>,
}

impl Level {
    fn new(point: usize) -> Self {
        let members = |set: usize| (2..=point).filter(move |&p| set & bit(p) != 0);
        let top = bit(point);
        // The sets with largest element l, other than {l} itself, have 2, …, l − 1 elements.
        let mut rounds: Vec<Round> = (1..point - 1)
            .map(|terms| Round {
                terms,
                targets: Vec::new(),
                sources: Vec::new(),
            })
            .collect();
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
                edge: short(edge(1, point)),
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
                    // Not reached for k ≤ 9, where a round has at most 6 terms.
                    let minima = round.sources.chunks_exact(terms);
                    for (&target, terms) in round.targets.iter().zip(minima) {
                        let costs = terms.iter().map(|&term| term.cost(states, edges));
                        states[usize::from(target) % STATES] = costs.min().unwrap_or(u64::MAX);
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

impl Term {
    /// f(S∖{j}, i) + `E_ij`.
    ///
    /// No sum can overflow: see `cell_sums`. Reducing a place modulo the length of its table
    /// changes nothing, since the places of a plan lie inside the tables; it shows this to the
    /// compiler.
    #[inline]
    fn cost(self, states: &[u64; STATES], edges: &[u64; EDGES]) -> u64 {
        states[usize::from(self.state) % STATES] + edges[usize::from(self.edge) % EDGES]
    }
}

/// The least of the given terms f(S∖{j}, i) + `E_ij`.
#[inline]
fn least<const TERMS: usize>(
    terms: &[Term; TERMS],
    states: &[u64; STATES],
    edges: &[u64; EDGES],
) -> u64 {
    least_of(terms.map(|term| term.cost(states, edges)))
}

/// The least of `COUNT` ≥ 1 numbers.
///
/// The numbers are compared in pairs, the first with the one after the middle and so on, and
/// then the smaller ones of the pairs in the same way, until one is left. The result is that
/// of comparing them one after the other, but each comparison waits for few earlier ones,
/// which a processor carries out faster.
#[inline]
fn least_of<const COUNT: usize>(mut numbers: [u64; COUNT]) -> u64 {
    let mut count = COUNT;
    while count > 1 {
        let half = count.div_ceil(2);
        for place in half..count {
            numbers[place - half] = numbers[place - half].min(numbers[place]);
        }
        count = half;
    }
    numbers[0]
}

/// One candidate f(S, i) + f(A∖S, j) for P(i, j), by the places of its two parts.
#[derive(Clone, Copy)]
struct Split {
    before: u16,
    after: u16,
}

/// P(i, j) for two points 2 ≤ i < j: the least of 2^(k−4) candidates, one for each set S of
/// points other than point 1 with i in S and j not in S.
struct Join {
    i: usize,
    j: usize,
    splits: Vec<Split>,
}

/// The order of the computation for blocks of k gaps; it depends on k alone.
struct Plan {
    /// The levels of the points 2, …, k − 1.
    levels: Vec<Level>,
    /// The places of f(A, j) for j = 2, …, k − 1, where A = {2, …, k − 1}.
    whole: Vec<u16>,
    /// One entry for each pair of points 2 ≤ i < j ≤ k − 1.
    joins: Vec<Join>,
}

impl Plan {
    fn new(k: usize) -> Self {
        // A as a bit mask; it is empty for k = 2.
        let all = (1 << (k - 2)) - 1;
        let mut joins = Vec::new();
        for i in 2..k {
            for j in i + 1..k {
                let splits = (1..all)
                    .filter(|set| set & bit(i) != 0 && set & bit(j) == 0)
                    .map(|set| Split {
                        before: short(place(set, i)),
                        after: short(place(all ^ set, j)),
                    })
                    .collect();
                joins.push(Join { i, j, splits });
            }
        }
        Self {
            levels: (2..k).map(Level::new).collect(),
            whole: (2..k).map(|end| short(place(all, end))).collect(),
            joins,
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
    /// For 1 ≤ i < j ≤ k − 1, the row Tab(κ(i, j), ·) of the current inner tuple.
    rows: [[&'a [u64]; POINTS]; POINTS],
    /// For an interior point i and a cell g_1, the row Tab(κ(0, i), ·), at the place [i][g_1].
    first: [[&'a [u64]; MAX_CELLS]; POINTS],
    /// For an interior point j and a cell g_k, the row Tab(κ(j, k), ·), at the place [j][g_k].
    last: [[&'a [u64]; MAX_CELLS]; POINTS],
    /// The interior heights fixed so far.
    heights: [usize; POINTS],
    /// The edge costs between the interior points whose heights are fixed.
    edges: [u64; EDGES],
    /// The table of f.
    states: [u64; STATES],
    /// P(i, j) at the place [i − 1][j − 1].
    through: [[u64; INTERIOR]; INTERIOR],
    /// `E_0i` for the interior points i whose heights are fixed, at the place
    /// [g_1·n + a_0][i − 1].
    from_start: Vec<[u64; INTERIOR]>,
    /// `E_jk` for the interior points j whose heights are fixed, at the place
    /// [g_k·n + a_k][j − 1].
    to_end: Vec<[u64; INTERIOR]>,
    /// reach(j) at the place [g_1·n + a_0][j − 1].
    reach: Vec<[u64; INTERIOR]>,
    /// The sums of the costs so far for the height of point 1 in hand, at the place g_1 + m·g_k.
    part: Vec<u128>,
}

impl<'a> Walker<'a> {
    fn new(plan: &'a Plan, keys: &'a Keys, table: &'a [u64], params: &Params) -> Self {
        let (cells, n) = (params.cells(), params.n);
        Self {
            plan,
            keys,
            table,
            cells,
            k: params.k,
            n,
            rows: [[&[]; POINTS]; POINTS],
            first: [[&[]; MAX_CELLS]; POINTS],
            last: [[&[]; MAX_CELLS]; POINTS],
            heights: [0; POINTS],
            edges: [0; EDGES],
            states: [0; STATES],
            through: [[0; INTERIOR]; INTERIOR],
            from_start: vec![[0; INTERIOR]; cells * n],
            to_end: vec![[0; INTERIOR]; cells * n],
            reach: vec![[0; INTERIOR]; cells * n],
            part: vec![0; cells * cells],
        }
    }

    /// The row Tab(κ, ·) of a key.
    fn row(&self, key: Key) -> Outcome<&'a [u64]> {
        let Some(rank) = self.keys.rank(key) else {
            return invalid("internal error: a key is missing".to_string());
        };
        Ok(&self.table[rank * self.n..][..self.n])
    }

    /// The cell sums `S_g` of the m² gap tuples g = (g_1, g_2, …, g_{k−1}, g_k) that have the
    /// inner tuple (g_2, …, g_{k−1}) with the given number; the sum for g_1 and g_k is at the
    /// place g_1 + m·g_k.
    fn block(&mut self, inner: usize) -> Outcome<Vec<u128>> {
        let (k, n, m) = (self.k, self.n, self.cells);
        if !(2..=MAX_GAPS).contains(&k) || m > MAX_CELLS {
            return invalid("internal error: k or m is out of range".to_string());
        }
        // g_2, …, g_{k−1} are the digits of the number of the inner tuple in base m, the lowest
        // first; g_i is kept at `gaps[i − 1]`.
        let mut gaps = [0; MAX_GAPS];
        let mut rest = inner;
        for gap in &mut gaps[1..k - 1] {
            *gap = rest % m;
            rest /= m;
        }
        // Shared paths (Section 7): E_ij depends on g only through g_{i+1}, …, g_j. So the rows of
        // Tab for two interior points are those of the inner tuple, whatever g_1 and g_k are;
        // the rows for point 0 and an interior point depend on g_1 as well, and those for an
        // interior point and point k on g_k, and there is one of them for each cell of that gap.
        //
        // Between interior points: κ(i, j) counts the entries of (g_{i+1}, …, g_j) by cell.
        for i in 1..k - 1 {
            let mut key = [0; MAX_CELLS];
            for j in i + 1..k {
                key[gaps[j - 1]] += 1;
                self.rows[i][j] = self.row(key)?;
            }
        }
        // From point 0: κ(0, i) counts g_1 and the entries of (g_2, …, g_i) by cell.
        for g_1 in 0..m {
            let mut key = [0; MAX_CELLS];
            key[g_1] += 1;
            for i in 1..k {
                if i >= 2 {
                    key[gaps[i - 1]] += 1;
                }
                self.first[i][g_1] = self.row(key)?;
            }
        }
        // To point k: κ(j, k) counts the entries of (g_{j+1}, …, g_{k−1}) and g_k by cell.
        for g_k in 0..m {
            let mut key = [0; MAX_CELLS];
            key[g_k] += 1;
            for j in (1..k).rev() {
                if j <= k - 2 {
                    key[gaps[j]] += 1;
                }
                self.last[j][g_k] = self.row(key)?;
            }
        }
        // Reflection (Section 7): only the heights y ≤ n − 1 − y of point 1 are gone through. A
        // height y < n − 1 − y counts twice; the middle height of an odd n counts once.
        let mut sums = vec![0; m * m];
        for height in 0..n {
            let mirror = n - 1 - height;
            if height > mirror {
                break;
            }
            let weight = if height < mirror { 2 } else { 1 };
            self.part.fill(0);
            self.fix(1, height);
            self.descend(2);
            for (sum, &part) in sums.iter_mut().zip(&self.part) {
                *sum += weight * part;
            }
        }
        Ok(sums)
    }

    /// Fixes the height of the interior point `point`; the heights of the interior points before
    /// it are fixed already.
    fn fix(&mut self, point: usize, height: usize) {
        self.heights[point] = height;
        // The edges from this point to the points 0 and k, for every cell of the gap at that
        // end and every height of that end.
        for g in 0..self.cells {
            let (first, last) = (self.first[point][g], self.last[point][g]);
            for a in 0..self.n {
                let difference = a.abs_diff(height);
                self.from_start[g * self.n + a][point - 1] = first[difference];
                self.to_end[g * self.n + a][point - 1] = last[difference];
            }
        }
        // The edges from this point to the interior points before it, and the values of f that
        // they complete.
        if point >= 2 {
            for earlier in 1..point {
                let difference = height.abs_diff(self.heights[earlier]);
                self.edges[edge(earlier, point)] = self.rows[earlier][point][difference];
            }
            self.plan.levels[point - 2].apply(&mut self.states, &self.edges);
        }
    }

    /// Runs through the heights of the points `point`, …, k − 1, the heights before being
    /// fixed, and adds the costs.
    fn descend(&mut self, point: usize) {
        if point < self.k {
            for height in 0..self.n {
                self.fix(point, height);
                self.descend(point + 1);
            }
            return;
        }
        // All interior heights are fixed. There are k − 1 interior points.
        match self.k - 1 {
            1 => self.finish::<1>(),
            2 => self.finish::<2>(),
            3 => self.finish::<3>(),
            4 => self.finish::<4>(),
            5 => self.finish::<5>(),
            6 => self.finish::<6>(),
            7 => self.finish::<7>(),
            8 => self.finish::<8>(),
            _ => unreachable!("`block` has checked that k is at most 9"),
        }
    }

    /// Adds cost(g, a) for the m² choices of g_1 and g_k and the n² heights of the points 0 and
    /// k, the interior heights being fixed. P is computed once here (Shared paths, Section 7);
    /// the edges at the two ends are taken for each g_1 and a_0 and each g_k and a_k separately.
    /// `N` must be k − 1, the number of interior points; the compiler, knowing it, can write
    /// out the loops over the interior points.
    fn finish<const N: usize>(&mut self) {
        if N >= 2 {
            self.join();
        }
        self.reach::<N>();
        self.add_costs::<N>();
    }

    /// P(i, j) for all interior points i ≠ j, from the table of f.
    fn join(&mut self) {
        // P(1, j) = P(j, 1) = f(A, j).
        for (j, &whole) in self.plan.whole.iter().enumerate() {
            let cost = self.states[usize::from(whole) % STATES];
            self.through[0][j + 1] = cost;
            self.through[j + 1][0] = cost;
        }
        // P(i, j) = P(j, i) = min over S of f(S, i) + f(A∖S, j).
        let states = &self.states;
        let cost = |split: &Split| {
            states[usize::from(split.before) % STATES] + states[usize::from(split.after) % STATES]
        };
        for join in &self.plan.joins {
            // Four minima side by side, each over a quarter of the candidates, and then the
            // least of the four.
            let (fours, rest) = join.splits.as_chunks::<4>();
            let mut best = [u64::MAX; 4];
            for four in fours {
                for (best, split) in best.iter_mut().zip(four) {
                    *best = (*best).min(cost(split));
                }
            }
            for split in rest {
                best[0] = best[0].min(cost(split));
            }
            let best = least_of(best);
            self.through[join.i - 1][join.j - 1] = best;
            self.through[join.j - 1][join.i - 1] = best;
        }
    }

    /// reach(j) for every interior point j and all g_1 and a_0.
    fn reach<const N: usize>(&mut self) {
        for (reach, first) in self.reach.iter_mut().zip(&self.from_start) {
            if N == 1 {
                // The only interior point: reach(1) = E_01.
                reach[0] = first[0];
                continue;
            }
            for (j, reach) in reach.iter_mut().enumerate().take(N) {
                // i = j stays out of the minimum.
                *reach = least_of::<N>(std::array::from_fn(|i| {
                    if i == j {
                        u64::MAX
                    } else {
                        first[i] + self.through[i][j]
                    }
                }));
            }
        }
    }

    /// cost(g, a) = min over j of reach(j) + `E_jk`, added to the sum of its g_1 and g_k.
    fn add_costs<const N: usize>(&mut self) {
        let (n, m) = (self.n, self.cells);
        for (start, reach) in self.reach.iter().enumerate() {
            // `start` is g_1·n + a_0.
            let g_1 = start / n;
            for (g_k, group) in self.to_end.chunks_exact(n).enumerate() {
                // The n heights of point k. Their costs are added in 64 bits, which `cell_sums`
                // has checked to be enough for n costs.
                let mut sum = 0;
                for last in group {
                    sum += least_of::<N>(std::array::from_fn(|j| reach[j] + last[j]));
                }
                self.part[g_1 + m * g_k] += u128::from(sum);
            }
        }
    }
}

/// Reports on the standard error stream how far the cell sums have come.
struct Progress {
    started: Instant,
    count: usize,
    finished: AtomicUsize,
    /// When the last message was written, in seconds after the start.
    told: AtomicU64,
}

impl Progress {
    /// Counts `sums` more cell sums and says so at every tenth of the way, unless the work is
    /// short, and once a minute if the tenths are further apart.
    fn step(&self, sums: usize) {
        let finished = self.finished.fetch_add(sums, Ordering::Relaxed) + sums;
        let tenths = finished * 10 / self.count;
        let elapsed = self.started.elapsed();
        let now = elapsed.as_secs();
        let told = self.told.load(Ordering::Relaxed);
        let tenth = tenths != (finished - sums) * 10 / self.count;
        if tenth && elapsed < Duration::from_secs(2) || !tenth && now < told + 60 {
            return;
        }
        let exchanged = self
            .told
            .compare_exchange(told, now, Ordering::Relaxed, Ordering::Relaxed);
        if tenth || exchanged.is_ok() {
            note(&format!(
                "rchk: {finished} of {} cell sums after {now} s",
                self.count
            ));
        }
    }
}

/// What a thread has computed: the numbers of some inner tuples, each with its m² cell sums as
/// `Walker::block` gives them.
type Blocks = Vec<(usize, Vec<u128>)>;

/// The number of the inner tuple (g_{k−1}, …, g_2), where `inner` is the number of the inner
/// tuple (g_2, …, g_{k−1}): its k − 2 digits in base m in the opposite order.
fn backwards(inner: usize, cells: usize, k: usize) -> usize {
    let mut rest = inner;
    let mut number = 0;
    for _ in 2..k {
        number = number * cells + rest % cells;
        rest /= cells;
    }
    number
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
    // The bound that covers the 64-bit arithmetic of this file. Every sum of two numbers that
    // is formed before the costs are added up is the cost of a path with at most k edges:
    // f(S∖{j}, i) + E_ij, f(S, i) + f(A∖S, j), E_0i + P(i, j) and reach(j) + E_jk are such
    // sums. An edge costs at most the largest entry of Tab, so each sum is at most k times that
    // entry, which is `bound`. The costs are then added up in 64 bits for the n heights of
    // point k only, which gives at most n·`bound`. So if n·`bound` fits in 64 bits, as is
    // checked here, none of these additions can overflow.
    let largest = u128::from(table.iter().copied().max().unwrap_or(0));
    let bound = mul(wide(params.k), largest, "the bound for cost(g, a)")?;
    narrow(mul(bound, wide(params.n), "n·cost")?, "n·cost")?;
    raise(&mut sizes.cost, bound);
    // A cell sum is a sum of n^(k+1) costs, so it is at most the number `all`, which is checked
    // to fit in 128 bits. The sums over more than the n heights of point k are kept in 128
    // bits; each is a part of a cell sum, or, where a part is counted twice for a height and
    // its mirror image, again at most the cell sum, so none of them can overflow.
    let tuples = power(wide(params.n), params.k + 1, "n^(k+1)")?;
    let all = mul(bound, tuples, "k·max(Tab)·n^(k+1)")?;
    raise(&mut sizes.cell_sum_bound, all);

    let cells = params.cells();
    let count = power(wide(cells), params.k, "m^k")?;
    let count = length(count, "the number of gap tuples")?;
    // There are m^(k−2) inner tuples (g_2, …, g_{k−1}); the gap tuple (g_1, …, g_k) has the
    // index g_1 + m·(the number of its inner tuple) + m^(k−1)·g_k.
    let inner_count = count / (cells * cells);
    let high = count / cells;
    let plan = Plan::new(params.k);
    let next = AtomicUsize::new(0);
    let progress = Progress {
        started: Instant::now(),
        count,
        finished: AtomicUsize::new(0),
        told: AtomicU64::new(0),
    };
    // Reversal (Section 7): S_g is the same for g and for g′ = (g_k, g_{k−1}, …, g_2, g_1), whose
    // inner tuple is that of g read backwards. Of an inner tuple and the one read backwards only
    // the one with the smaller number is computed, and each of its m² sums is stored for g and
    // for g′ (below). An inner tuple that reads the same backwards is computed, and its sums are
    // stored once.
    //
    // Each thread takes the next inner tuple that no thread has taken, until none is left. A
    // sum depends on its gap tuple alone, so the result does not depend on the number of
    // threads.
    let work = || -> Outcome<Blocks> {
        let mut walker = Box::new(Walker::new(&plan, keys, table, params));
        let mut found = Vec::new();
        loop {
            let inner = next.fetch_add(1, Ordering::Relaxed);
            if inner >= inner_count {
                return Ok(found);
            }
            let mirror = backwards(inner, cells, params.k);
            if mirror < inner {
                continue;
            }
            found.push((inner, walker.block(inner)?));
            let both = if mirror == inner { 1 } else { 2 };
            progress.step(both * cells * cells);
        }
    };
    let parts: Vec<Outcome<Blocks>> = thread::scope(|scope| {
        // More threads than inner tuples would find nothing to do.
        let handles: Vec<_> = (0..threads.min(inner_count))
            .map(|_| scope.spawn(work))
            .collect();
        let stopped = || invalid("internal error: a thread stopped".to_string());
        handles
            .into_iter()
            .map(|handle| handle.join().unwrap_or_else(|_| stopped()))
            .collect()
    });

    // The sum at the place g_1 + m·g_k of the block of an inner tuple is S_g and, by Reversal,
    // S_g′. Every gap tuple must receive its sum exactly once; otherwise status 2.
    let mut sums = vec![None; count];
    let mut store = |index: usize, sum: u128| -> Outcome<()> {
        if sums[index].replace(sum).is_some() {
            return invalid("internal error: a cell sum is computed twice".to_string());
        }
        Ok(())
    };
    for part in parts {
        for (inner, block) in part? {
            let mirror = backwards(inner, cells, params.k);
            for (place, &sum) in block.iter().enumerate() {
                let (g_1, g_k) = (place % cells, place / cells);
                store(g_1 + cells * inner + high * g_k, sum)?;
                if mirror != inner {
                    store(g_k + cells * mirror + high * g_1, sum)?;
                }
                raise(&mut sizes.cell_sum, sum);
            }
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
    /// by trying every order; `visited` has the bit i for the interior point i.
    fn cheapest(e: &[[u64; POINTS]; POINTS], k: usize, at: usize, visited: usize) -> u64 {
        if visited == (1 << k) - 2 {
            return e[at][k];
        }
        (1..k)
            .filter(|&next| visited & (1 << next) == 0)
            .map(|next| e[at][next] + cheapest(e, k, next, visited | (1 << next)))
            .min()
            .unwrap()
    }

    /// `S_g` straight from the definitions of Section 7: every height tuple, every order.
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

    /// `S_g` for one gap tuple, as this program computes it: from the block of its inner tuple.
    fn sum_by_block(walker: &mut Walker, index: usize) -> u128 {
        let (m, k) = (walker.cells, walker.k);
        let high = m.pow(u32::try_from(k - 1).unwrap());
        let (g_1, inner, g_k) = (index % m, index % high / m, index / high);
        walker.block(inner).unwrap()[g_1 + m * g_k]
    }

    #[test]
    fn the_plan_has_every_value_once() {
        for k in 2..=MAX_GAPS {
            let others = k - 2;
            let plan = Plan::new(k);
            assert_eq!(plan.levels.len(), others);
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
            // There are j·C(k − 2, j) pairs (S, j) with |S| = j, hence (k − 2)·2^(k − 3) values,
            // and each value with |S| ≥ 2 is a minimum of |S| − 1 terms.
            let values = if others == 0 {
                0
            } else {
                others << (others - 1)
            };
            assert_eq!(targets.len(), values);
            let mut distinct = targets.clone();
            distinct.sort_unstable();
            distinct.dedup();
            assert_eq!(distinct.len(), targets.len());
            if others >= 2 {
                assert_eq!(terms, (others * (others - 1)) << (others - 2));
            }
            assert_eq!(plan.whole.len(), others);
            assert!(plan.whole.iter().all(|end| targets.contains(end)));

            // The candidates for P(i, j): one for each set S with i in S and j not in S; the two
            // sets of a candidate are disjoint, and together they are A.
            let all = (1_usize << others) - 1;
            assert_eq!(plan.joins.len(), others * others.saturating_sub(1) / 2);
            for join in &plan.joins {
                assert!(2 <= join.i && join.i < join.j && join.j < k);
                assert_eq!(join.splits.len(), 1 << (others - 2));
                let mut sets = Vec::new();
                for split in &join.splits {
                    let (before, after) = (usize::from(split.before), usize::from(split.after));
                    assert!(targets.contains(&split.before) && targets.contains(&split.after));
                    assert_eq!((before % ENDS + 2, after % ENDS + 2), (join.i, join.j));
                    let (near, far) = (before / ENDS, after / ENDS);
                    assert!(near & bit(join.i) != 0 && far & bit(join.j) != 0);
                    assert_eq!((near & far, near | far), (0, all));
                    sets.push(near);
                }
                sets.sort_unstable();
                sets.dedup();
                assert_eq!(sets.len(), join.splits.len());
            }
            let mut pairs: Vec<_> = plan.joins.iter().map(|join| (join.i, join.j)).collect();
            pairs.dedup();
            assert_eq!(pairs.len(), plan.joins.len());
        }
    }

    #[test]
    fn an_inner_tuple_is_read_backwards() {
        // k = 5, m = 3: (g_2, g_3, g_4) = (1, 0, 2) has the number 1 + 0·3 + 2·9, and (2, 0, 1)
        // has the number 2 + 0·3 + 1·9.
        assert_eq!(backwards(19, 3, 5), 11);
        // k = 6, m = 4: (3, 0, 1, 2) and (2, 1, 0, 3).
        assert_eq!(backwards(3 + 16 + 2 * 64, 4, 6), 2 + 4 + 3 * 64);
        // No inner gap, and one.
        assert_eq!(backwards(0, 4, 2), 0);
        assert_eq!(backwards(3, 4, 3), 3);
        for (k, cells) in [(2, 3), (3, 4), (4, 3), (5, 4), (6, 2), (9, 2), (9, 3)] {
            let count = usize::pow(cells, u32::try_from(k - 2).unwrap());
            for inner in 0..count {
                let mirror = backwards(inner, cells, k);
                assert!(mirror < count);
                assert_eq!(backwards(mirror, cells, k), inner);
            }
        }
    }

    /// All cell sums of small cases, among them k = 2 and k = 3 (no and one inner gap), a single
    /// gap cell, a single height cell, and odd and even numbers of height cells.
    #[test]
    fn all_cell_sums_of_small_cases_agree_with_a_search_over_all_orders() {
        let mut random = Random(7);
        let cases = [
            (2, 1, 1),
            (2, 1, 2),
            (2, 1, 3),
            (2, 2, 1),
            (2, 2, 5),
            (2, 3, 4),
            (3, 1, 1),
            (3, 1, 3),
            (3, 2, 1),
            (3, 2, 4),
            (3, 3, 3),
            (3, 4, 2),
            (4, 1, 1),
            (4, 1, 5),
            (4, 2, 3),
            (4, 3, 2),
            (4, 4, 1),
            (5, 1, 4),
            (5, 2, 3),
            (5, 3, 2),
            (6, 1, 3),
            (6, 2, 2),
            (6, 3, 1),
            (7, 1, 3),
            (7, 2, 2),
            (8, 1, 2),
            (8, 2, 1),
            (9, 1, 2),
            (9, 2, 1),
        ];
        for (k, cells, n) in cases {
            let params = params(k, cells, n);
            let keys = Keys::new(cells, u8::try_from(k).unwrap());
            let table = random_table(&keys, n, &mut random);
            let mut sizes = Sizes::default();
            let sums = cell_sums(&params, &keys, &table, 2, &mut sizes).unwrap();
            assert_eq!(sums.len(), cells.pow(u32::try_from(k).unwrap()));
            for (index, &sum) in sums.iter().enumerate() {
                assert_eq!(
                    sum,
                    sum_by_search(&params, &keys, &table, index),
                    "k = {k}, m = {cells}, n = {n}, index {index}"
                );
            }
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
            (5, 2, 3),
            (6, 2, 2),
            (6, 6, 2),
            (6, 2, 3),
            (7, 3, 2),
            (7, 7, 1),
            (8, 2, 2),
            (8, 8, 1),
            (9, 2, 2),
            (9, 3, 2),
            (9, 8, 1),
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
                    sum_by_block(&mut walker, index),
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
        // It is the bound checked beforehand that refuses it, not a sum that overflows later.
        let refused = cell_sums(&params, &keys, &table, 1, &mut sizes);
        assert!(matches!(refused, Err(Stop::Invalid(reason)) if reason.contains("n·cost")));
    }

    /// Eight gap tuples of nine gaps, each in the order g_1, …, g_9.
    const NINE_GAPS: [[usize; 9]; 8] = [
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
        [3, 3, 3, 3, 3, 3, 3, 3, 3],
        [0, 1, 2, 3, 0, 1, 2, 3, 0],
        [3, 0, 2, 1, 1, 3, 0, 2, 1],
        [1, 2, 0, 0, 3, 1, 2, 2, 0],
        [2, 3, 1, 0, 0, 2, 3, 1, 3],
        [1, 1, 1, 2, 2, 2, 0, 0, 3],
        [0, 3, 0, 3, 1, 2, 1, 2, 2],
    ];

    /// Not run by default, since it takes a minute or two: the cell sums of `data/specs/k9.txt`
    /// for the gap tuples that share their inner tuple with one of the eight tuples above (16
    /// for each), compared with `data/values/k9.txt`, both at their own places and at those of
    /// the gap tuples read backwards. It also prints the sizes that Section 9 is about; those of
    /// Section 8 are found from the stored cell sums, which this test does not confirm. Run it
    /// with `cargo test --release -- --ignored --nocapture nine_gaps`.
    #[test]
    #[ignore = "takes a minute or two"]
    fn cell_sums_for_nine_gaps_agree_with_the_values_file() {
        let folder = concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/");
        let read = |name: &str| std::fs::read_to_string(format!("{folder}{name}")).unwrap();
        let spec = crate::files::Spec::parse("spec", &read("specs/k9.txt")).unwrap();
        let values = crate::files::Values::parse("values", &read("values/k9.txt")).unwrap();
        let params = &spec.params;
        assert_eq!((params.k, params.cells(), params.n), (9, 4, 6));
        let keys = Keys::new(4, 9);
        let mut sizes = Sizes::default();
        let tables = crate::tables::build(params, &keys, &mut sizes).unwrap();
        for (row, stored) in tables.table.chunks_exact(params.n).zip(&values.table) {
            let row: Vec<u128> = row.iter().map(|&entry| u128::from(entry)).collect();
            assert_eq!(row, stored[4..]);
        }
        println!("the table of {} keys agrees", keys.len());
        let plan = Plan::new(9);
        let mut walker = Walker::new(&plan, &keys, &tables.table, params);
        let high = 4_usize.pow(8);
        for gaps in NINE_GAPS {
            let index = gaps.iter().rev().fold(0, |index, gap| index * 4 + gap);
            let inner = index % high / 4;
            let mirror = backwards(inner, 4, 9);
            let started = Instant::now();
            let block = walker.block(inner).unwrap();
            for (place, &sum) in block.iter().enumerate() {
                let (g_1, g_9) = (place % 4, place / 4);
                let other = g_1 + 4 * inner + high * g_9;
                assert_eq!(sum, values.sums[other], "gap tuple {other}");
                let reversed = g_9 + 4 * mirror + high * g_1;
                assert_eq!(sum, values.sums[reversed], "gap tuple {reversed}");
            }
            println!(
                "gap tuple {index}: {}, stored {}; the 16 sums of its inner tuple agree ({} ms)",
                block[index % 4 + 4 * (index / high)],
                values.sums[index],
                started.elapsed().as_millis()
            );
        }

        let largest = u128::from(tables.table.iter().copied().max().unwrap());
        sizes.cost = 9 * largest;
        sizes.cell_sum_bound = 9 * largest * 6_u128.pow(10);
        sizes.cell_sum = values.sums.iter().copied().max().unwrap();
        let total = crate::total::total(&tables.masses, &values.sums, 9, &mut sizes).unwrap();
        assert_eq!(total, values.total);
        let verdict = crate::total::test(total, params, spec.threshold, &mut sizes).unwrap();
        assert!(verdict.accepted);
        println!("the stored total is the total of the stored cell sums; the test holds for it");
        println!(
            "n·k·max(Tab): {} binary digits",
            crate::arith::bit_length(6 * 9 * largest)
        );
        for line in sizes.report() {
            println!("{line}");
        }
    }

    /// Not a test: the time for the cell sums of one inner tuple, with n = 6 and m = 4, on a
    /// table of random numbers. Run it with
    /// `cargo test --release -- --ignored --nocapture timing`.
    #[test]
    #[ignore = "a measurement, not a test"]
    fn timing_for_seven_and_nine_gaps() {
        let mut random = Random(6);
        for (k, blocks) in [(7_u8, 12), (9, 3)] {
            let params = params(usize::from(k), 4, 6);
            let keys = Keys::new(4, k);
            let table = random_table(&keys, 6, &mut random);
            let plan = Plan::new(usize::from(k));
            let mut walker = Walker::new(&plan, &keys, &table, &params);
            let tuples = 16 * 6_u128.pow(u32::from(k) + 1);
            let (mut best, mut all) = (u128::MAX, 0);
            for inner in 0..blocks {
                let started = Instant::now();
                walker.block(inner * 80 + 7).unwrap();
                let time = started.elapsed().as_nanos() * 1000 / tuples;
                best = best.min(time);
                all += time;
            }
            let mean = all / wide(blocks);
            println!(
                "k = {k}, {blocks} inner tuples: {}.{:03} ns for a gap tuple and a height tuple \
                 on average, {}.{:03} ns at best",
                mean / 1000,
                mean % 1000,
                best / 1000,
                best % 1000
            );
        }
    }
}
