//! Sections 2–6 of RECIPE.md: from the parameters to the table Tab.

use crate::arith::{
    add, ceil_div, ceil_sqrt, floor_div, length, mul, narrow, raise, sub, wide, MAX_ENTRIES,
};
use crate::failure::{invalid, Outcome, Stop};
use crate::files::Params;
use crate::keys::{gaps_of, Keys};
use crate::sizes::Sizes;

/// Q = 2^62, the scale of the bounds for the exponential function.
const Q: u128 = 1 << 62;
/// D = 2^48, the scale of weights and probabilities.
pub const D: u128 = 1 << 48;
/// F = 2^32, the scale of lengths.
pub const F: u128 = 1 << 32;

/// What the later sections and the comparison with the values file need.
pub struct Tables {
    /// P_c for every gap cell (Section 3).
    pub masses: Vec<u128>,
    /// E_T (Section 3).
    pub tail_term: u128,
    /// Tab (Section 6) by rows: the entry for the key of rank r and the height difference d is
    /// at position r·n + d.
    pub table: Vec<u64>,
}

/// Carries out Sections 2–6.
pub fn build(params: &Params, keys: &Keys, sizes: &mut Sizes) -> Outcome<Tables> {
    let grid = Grid::new(params)?;
    let mesh = u128::from(params.mesh);
    let powers = exponentials(mesh, grid.last_start().max(grid.tail_width()), sizes)?;
    let cells = cells(mesh, &grid, &powers, sizes)?;
    let lengths = lengths(params, &grid, sizes)?;
    let table = table(params, keys, &grid, &cells, &lengths, sizes)?;
    Ok(Tables {
        masses: cells.masses,
        tail_term: cells.tail_term,
        table,
    })
}

/// The mesh points of the gap cells (Section 1).
struct Grid {
    /// b_0 = 0, b_1, …, b_{m−1}.
    starts: Vec<usize>,
    /// n_0, …, n_{m−1}; the last one is N_T = T·M.
    widths: Vec<usize>,
}

impl Grid {
    fn new(params: &Params) -> Outcome<Self> {
        let mut starts = vec![0];
        for &boundary in &params.boundaries {
            starts.push(length(u128::from(boundary), "a boundary of the gap cells")?);
        }
        let mut widths: Vec<usize> = starts.windows(2).map(|pair| pair[1] - pair[0]).collect();
        let tail = u128::from(params.tail) * u128::from(params.mesh);
        widths.push(length(tail, "N_T")?);
        Ok(Self { starts, widths })
    }

    /// b_{m−1}.
    fn last_start(&self) -> usize {
        self.starts[self.starts.len() - 1]
    }

    /// N_T.
    fn tail_width(&self) -> usize {
        self.widths[self.widths.len() - 1]
    }
}

/// Bounds for e^(−1/M) and its powers (Section 2): `lo_1 ≤ Q·e^(−1/M) ≤ up_1` and
/// `lo[i] ≤ Q·e^(−i/M) ≤ up[i]`.
struct Exponentials {
    lo_1: u128,
    up_1: u128,
    /// Rlo.
    lo: Vec<u128>,
    /// Rup.
    up: Vec<u128>,
}

/// Section 2, for the exponents 0, …, `last`.
fn exponentials(mesh: u128, last: usize, sizes: &mut Sizes) -> Outcome<Exponentials> {
    // lo_13 = 0 and up_13 = Q; each step uses both values of the step before.
    let (mut lo, mut up) = (0, Q);
    for j in (1..=12).rev() {
        let divisor = mesh * j;
        (lo, up) = (
            sub(Q, ceil_div(up, divisor, "up_{j+1}/(M·j)")?, "lo_j")?,
            sub(Q, floor_div(lo, divisor, "lo_{j+1}/(M·j)")?, "up_j")?,
        );
    }
    let mut powers = Exponentials {
        lo_1: lo,
        up_1: up,
        lo: vec![Q],
        up: vec![Q],
    };
    for i in 1..=last {
        let above = mul(powers.up[i - 1], powers.up_1, "Rup[i−1]·up_1")?;
        let below = mul(powers.lo[i - 1], powers.lo_1, "Rlo[i−1]·lo_1")?;
        raise(&mut sizes.power_product, above.max(below));
        powers.up.push(ceil_div(above, Q, "Rup[i]")?);
        powers.lo.push(floor_div(below, Q, "Rlo[i]")?);
    }
    for &value in powers.up.iter().chain(&powers.lo) {
        raise(&mut sizes.power, value);
    }
    Ok(powers)
}

/// The results of Section 3.
struct Cells {
    /// W_c(i) for 0 ≤ i ≤ n_c.
    weights: Vec<Vec<u64>>,
    /// P_c.
    masses: Vec<u128>,
    /// E_T.
    tail_term: u128,
}

/// Section 3.
fn cells(mesh: u128, grid: &Grid, powers: &Exponentials, sizes: &mut Sizes) -> Outcome<Cells> {
    let up = &powers.up;
    let c_lambda = sub(
        Q,
        mul(mesh, sub(Q, powers.up_1, "Q − up_1")?, "M·(Q − up_1)")?,
        "C_λ",
    )?;
    let c_mu = sub(
        mul(mesh, sub(Q, powers.lo_1, "Q − lo_1")?, "M·(Q − lo_1)")?,
        powers.lo_1,
        "C_μ",
    )?;
    raise(&mut sizes.constant, c_lambda.max(c_mu));

    // num_c(i); it depends on the cell only through n_c.
    let numerator = |i: usize, width: usize| -> Outcome<u128> {
        let mut value = 0;
        if i < width {
            value = mul(up[i], c_lambda, "Rup[i]·C_λ")?;
        }
        if i >= 1 {
            value = add(value, mul(up[i - 1], c_mu, "Rup[i−1]·C_μ")?, "num_c(i)")?;
        }
        Ok(value)
    };

    let last = grid.widths.len() - 1;
    let mut weights = Vec::with_capacity(grid.widths.len());
    let mut masses = Vec::with_capacity(grid.widths.len());
    for (c, &width) in grid.widths.iter().enumerate() {
        let mut row = Vec::with_capacity(width + 1);
        for i in 0..=width {
            let num = numerator(i, width)?;
            raise(&mut sizes.numerator, num);
            let weight = if c < last {
                let divisor = sub(Q, up[width], "Q − Rup[n_c]")?;
                ceil_div(num.div_ceil(1 << 14), divisor, "W_c(i)")?
            } else {
                // In the last cell the truncation point carries all that lies beyond it.
                let atom = if i == width {
                    up[width].div_ceil(1 << 14)
                } else {
                    0
                };
                add(num.div_ceil(1 << 76), atom, "W_{m−1}(i)")?
            };
            raise(&mut sizes.weight, weight);
            row.push(narrow(weight, "W_c(i)")?);
        }
        weights.push(row);

        let start = grid.starts[c];
        let difference = if c < last {
            sub(
                up[start],
                powers.lo[grid.starts[c + 1]],
                "Rup[b_c] − Rlo[b_{c+1}]",
            )?
        } else {
            up[start]
        };
        let mass = difference.div_ceil(1 << 14);
        raise(&mut sizes.mass, mass);
        masses.push(mass);
    }
    Ok(Cells {
        weights,
        masses,
        tail_term: up[grid.tail_width()].div_ceil(1 << 30),
    })
}

/// χ(t) for −ν ≤ t ≤ ν, at position t + ν (Section 5).
fn height_counts(nu: usize) -> Vec<u128> {
    let eta = |i: usize| -> u128 {
        if i == 0 || i == nu {
            1
        } else {
            2
        }
    };
    let mut counts = vec![0; 2 * nu + 1];
    for i in 0..=nu {
        for j in 0..=nu {
            counts[i + nu - j] += eta(i) * eta(j);
        }
    }
    counts
}

/// Section 5: G(j, d) for 0 ≤ j ≤ J and 0 ≤ d ≤ n − 1, at position j·n + d.
fn lengths(params: &Params, grid: &Grid, sizes: &mut Sizes) -> Outcome<Vec<u64>> {
    let (n, nu) = (params.n, params.nu);
    let reach = wide(params.k) * wide(grid.last_start() + grid.tail_width());
    let reach = length(reach, "J")?;
    length(wide(reach + 1) * wide(n), "the number of values G(j, d)")?;

    let counts = height_counts(nu);
    let four_nu_squared = wide(4 * nu * nu);
    if counts.iter().sum::<u128>() != four_nu_squared {
        return invalid("the numbers χ(t) do not add up to 4ν²".to_string());
    }

    let (h1, h2) = (u128::from(params.h1), u128::from(params.h2));
    let alpha = mul(mul(h2, h2, "h_2²")?, wide(n * nu), "α")?;
    let gamma = mul(u128::from(params.mesh), mul(h1, h1, "h_1²")?, "γ")?;
    let divisor = mul(alpha, u128::from(params.mesh), "α·M")?;
    let square = |factor: u128, index: usize, what: &str| -> Outcome<u128> {
        let product = mul(factor, wide(index), what)?;
        mul(product, product, what)
    };

    // (γ·τ)² for 0 ≤ τ ≤ n·ν. The squares increase with j and τ, so if the largest argument of
    // ceil_sqrt fits in 128 bits, all arguments do.
    let top = n * nu;
    let vertical: Vec<u128> = (0..=top)
        .map(|tau| square(gamma, tau, "(γ·τ)²"))
        .collect::<Outcome<_>>()?;
    let widest = add(
        square(alpha, reach, "(α·J)²")?,
        vertical[top],
        "(α·j)² + (γ·τ)²",
    )?;
    let argument = mul(widest, F * F, "the argument of ceil_sqrt")?;
    raise(&mut sizes.squares, widest);
    raise(&mut sizes.root_argument, argument);

    let mut lengths = Vec::with_capacity((reach + 1) * n);
    let mut dist = vec![0_u128; top + 1];
    for j in 0..=reach {
        let horizontal = square(alpha, j, "(α·j)²")?;
        for (slot, &squared) in dist.iter_mut().zip(&vertical) {
            let root = ceil_sqrt((horizontal + squared) * F * F);
            *slot = ceil_div(root, divisor, "Dist(j, τ)")?;
        }
        raise(&mut sizes.distance, dist[top]);
        for d in 0..n {
            // t = u − ν runs over −ν, …, ν, and τ = |d·ν + t|. A distance is at most 2^64 and
            // the numbers χ(t) add up to 4ν² ≤ 2^18, so the sum is below 2^83.
            let sum: u128 = counts
                .iter()
                .enumerate()
                .map(|(u, &count)| count * dist[(d * nu + u).abs_diff(nu)])
                .sum();
            raise(&mut sizes.height_sum, sum);
            let mean = ceil_div(sum, four_nu_squared, "G(j, d)")?;
            lengths.push(narrow(mean, "G(j, d)")?);
        }
    }
    Ok(lengths)
}

/// V_κ from V_κ′ and W_c (Section 4): the value at s is ceil( Σ_{i+j=s} V_κ′(i)·W_c(j) / D ).
fn convolve(shorter: &[u64], weights: &[u64], sizes: &mut Sizes) -> Outcome<Vec<u64>> {
    // A sum has at most min(len V_κ′, len W_c) terms, each at most max V_κ′ · max W_c. Once this
    // bound is known to fit in 128 bits, no sum below can overflow.
    let largest = |values: &[u64]| u128::from(values.iter().copied().max().unwrap_or(0));
    let terms = wide(shorter.len().min(weights.len()));
    mul(
        terms,
        largest(shorter) * largest(weights),
        "a sum in Section 4",
    )?;

    let len = shorter.len() + weights.len() - 1;
    let mut longer = Vec::with_capacity(len);
    for s in 0..len {
        // i runs from `low` to `high`, and j = s − i runs down from s − low to s − high.
        let low = s.saturating_sub(weights.len() - 1);
        let high = s.min(shorter.len() - 1);
        let sum: u128 = shorter[low..=high]
            .iter()
            .zip(weights[s - high..=s - low].iter().rev())
            .map(|(&v, &w)| u128::from(v) * u128::from(w))
            .sum();
        raise(&mut sizes.convolution, sum);
        let value = sum.div_ceil(D);
        raise(&mut sizes.weight, value);
        longer.push(narrow(value, "V_κ(s)")?);
    }
    Ok(longer)
}

/// Sections 4 and 6: the weight vector of every key, in key order, and from it the row of Tab.
fn table(
    params: &Params,
    keys: &Keys,
    grid: &Grid,
    cells: &Cells,
    lengths: &[u64],
    sizes: &mut Sizes,
) -> Outcome<Vec<u64>> {
    let n = params.n;
    let last = grid.widths.len() - 1;
    let longest = u128::from(lengths.iter().copied().max().unwrap_or(0));
    let broken = || Stop::Invalid("internal error in the weight vectors".to_string());

    // V_κ for the keys so far that can still be a κ′, that is, those with fewer than k gaps.
    let mut vectors: Vec<Vec<u64>> = Vec::with_capacity(keys.len());
    let mut kept = 0;
    let mut table = Vec::with_capacity(keys.len() * n);
    for key in keys.iter() {
        let gaps = gaps_of(*key);
        let cell = key
            .iter()
            .rposition(|&count| count > 0)
            .ok_or_else(broken)?;
        let vector = if gaps == 1 {
            cells.weights[cell].clone()
        } else {
            let mut shorter = *key;
            shorter[cell] -= 1;
            let rank = keys.rank(shorter).filter(|&rank| rank < vectors.len());
            convolve(
                &vectors[rank.ok_or_else(broken)?],
                &cells.weights[cell],
                sizes,
            )?
        };

        // b_κ and len_κ; the vector has the length len_κ by construction.
        let count = |c: usize| usize::from(key[c]);
        let base: usize = (0..=last).map(|c| count(c) * grid.starts[c]).sum();
        let len: usize = 1 + (0..=last).map(|c| count(c) * grid.widths[c]).sum::<usize>();
        if vector.len() != len {
            return Err(broken());
        }

        // The sums of Section 6 have len_κ terms, each at most max V_κ · max G; as in Section 4,
        // this bound is checked once.
        let heaviest = u128::from(vector.iter().copied().max().unwrap_or(0));
        mul(wide(len), heaviest * longest, "a sum in Section 6")?;
        let mut sums = vec![0_u128; n];
        for (s, &weight) in vector.iter().enumerate() {
            let row = &lengths[(base + s) * n..][..n];
            for (sum, &g) in sums.iter_mut().zip(row) {
                *sum += u128::from(weight) * u128::from(g);
            }
        }
        let tail = mul(wide(count(last)), cells.tail_term, "κ_{m−1}·E_T")?;
        for sum in sums {
            raise(&mut sizes.table_sum, sum);
            let entry = add(sum.div_ceil(D), tail, "Tab(κ, d)")?;
            raise(&mut sizes.table, entry);
            table.push(narrow(entry, "Tab(κ, d)")?);
        }

        if gaps < params.k {
            kept += len;
            if wide(kept) > MAX_ENTRIES {
                return invalid("the weight vectors need too much memory".to_string());
            }
            vectors.push(vector);
        } else {
            vectors.push(Vec::new());
        }
    }
    Ok(table)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn params(k: usize, h: (u64, u64), mesh: u64, boundaries: &[u64]) -> Params {
        Params {
            k,
            h1: h.0,
            h2: h.1,
            mesh,
            boundaries: boundaries.to_vec(),
            n: 6,
            nu: 64,
            tail: 16,
        }
    }

    #[test]
    fn the_bounds_for_the_exponential_function_are_close() {
        // Q·e^(−1/128) = 4575797593107614194.998…
        let mut sizes = Sizes::default();
        let powers = exponentials(128, 256, &mut sizes).unwrap();
        assert!(powers.lo_1 <= 4_575_797_593_107_614_194);
        assert!(powers.up_1 > 4_575_797_593_107_614_194);
        assert!(powers.up_1 - powers.lo_1 <= 4);
        // Q·e^(−2) = 624123833502197199.928… lies between the bounds for i = 256.
        assert!(powers.lo[256] <= 624_123_833_502_197_199);
        assert!(powers.up[256] > 624_123_833_502_197_199);
        assert!(powers.up[256] - powers.lo[256] < 1 << 10);
        // Q·e^(−1/2) = 2797128963144291324.959…; for M = 2 the twelve steps leave a gap of
        // about Q·(1/2)^12/12!, which is 2^21.2.
        let coarse = exponentials(2, 1, &mut sizes).unwrap();
        assert!(coarse.lo_1 <= 2_797_128_963_144_291_324);
        assert!(coarse.up_1 > 2_797_128_963_144_291_324);
        assert!(coarse.up_1 - coarse.lo_1 < 1 << 22);
        assert_eq!(powers.lo[0], Q);
        assert_eq!(powers.up[1], powers.up_1);
        assert_eq!(powers.lo[1], powers.lo_1);
    }

    #[test]
    fn the_weights_of_bounded_cells() {
        // M = 1023 and bounded cells of 2, 3 and 4 mesh intervals. The numbers follow from
        // Sections 2 and 3 of RECIPE.md by integer arithmetic. With the divisor Q − Rlo[n_c] in
        // place of Q − Rup[n_c], one weight of each cell would be smaller by 1; the stored numbers
        // of the spec files do not show such a change.
        let params = Params {
            k: 2,
            h1: 2,
            h2: 1,
            mesh: 1023,
            boundaries: vec![2, 5, 9],
            n: 2,
            nu: 1,
            tail: 1,
        };
        let grid = Grid::new(&params).unwrap();
        let mut sizes = Sizes::default();
        let last = grid.last_start().max(grid.tail_width());
        let powers = exponentials(1023, last, &mut sizes).unwrap();
        let cells = cells(1023, &grid, &powers, &mut sizes).unwrap();
        assert_eq!(
            cells.weights[0],
            [70_414_607_545_573, 140_737_477_148_674, 70_322_892_016_474]
        );
        assert_eq!(
            cells.weights[1],
            [
                46_966_011_783_208,
                93_870_835_051_172,
                93_779_119_538_148,
                46_859_010_338_195
            ]
        );
        assert_eq!(
            cells.weights[2],
            [
                35_241_719_503_539,
                70_437_525_198_150,
                70_368_704_954_289,
                70_299_951_950_524,
                35_127_075_104_221
            ]
        );
        // The weights of a cell add up to 1, which is D, up to the roundings.
        for row in &cells.weights[..3] {
            let sum: u128 = row.iter().map(|&weight| u128::from(weight)).sum();
            assert!((D..D + 100).contains(&sum));
        }
    }

    #[test]
    fn the_height_counts_add_up() {
        assert_eq!(height_counts(1), [1, 2, 1]);
        assert_eq!(height_counts(2), [1, 4, 6, 4, 1]);
        for nu in 1..=256 {
            let counts = height_counts(nu);
            assert_eq!(counts.iter().sum::<u128>(), wide(4 * nu * nu));
            assert!(counts.iter().eq(counts.iter().rev()));
        }
    }

    #[test]
    fn convolution_rounds_every_sum_up() {
        let mut sizes = Sizes::default();
        let half = u64::try_from(D / 2).unwrap();
        // (D/2, D/2) ∗ (D/2, D/2) = (D²/4, D²/2, D²/4), divided by D.
        assert_eq!(
            convolve(&[half, half], &[half, half], &mut sizes).unwrap(),
            [half / 2, half, half / 2]
        );
        // 3·5 = 15 and 3·7 + 4·5 = 41 and 4·7 = 28 are all rounded up to 1.
        assert_eq!(convolve(&[3, 4], &[5, 7], &mut sizes).unwrap(), [1, 1, 1]);
        assert_eq!(
            convolve(&[0, 4, 0], &[0, 7], &mut sizes).unwrap(),
            [0, 0, 1, 0]
        );
        assert_eq!(sizes.convolution, D * D / 2);
    }

    #[test]
    fn the_small_example() {
        // k = 3, h = 2, M = 16, cells [0, 11), [11, 28), [28, ∞), n = 3, ν = 4, T = 12: the
        // masses, the tail term and three rows of the table of its values file.
        let params = Params {
            k: 3,
            h1: 2,
            h2: 1,
            mesh: 16,
            boundaries: vec![11, 28],
            n: 3,
            nu: 4,
            tail: 12,
        };
        let keys = Keys::new(3, 3);
        let tables = build(&params, &keys, &mut Sizes::default()).unwrap();
        assert_eq!(
            tables.masses,
            [139_940_470_011_903, 92_621_490_013_121, 48_913_016_685_633]
        );
        assert_eq!(tables.tail_term, 26_390);
        assert_eq!(tables.table.len(), 19 * 3);
        assert_eq!(
            tables.table[..3],
            [12_087_143_222, 13_416_178_336, 16_756_528_437]
        );
        assert_eq!(
            tables.table[13 * 3..14 * 3],
            [18_135_361_683, 19_041_238_364, 21_518_199_412]
        );
        assert_eq!(
            tables.table[18 * 3..],
            [4_637_203_702, 7_205_937_300, 12_216_866_929]
        );
    }

    /// Carries out Sections 2–6 for the cells of the paper and checks the bounds that Section 9
    /// states for the quantities of these sections.
    fn assert_section_9(k: u8, h: (u64, u64)) {
        let mut sizes = Sizes::default();
        let keys = Keys::new(4, k);
        let params = params(usize::from(k), h, 128, &[48, 112, 208]);
        build(&params, &keys, &mut sizes).unwrap();
        println!("k = {k}, h = {}/{}:", h.0, h.1);
        for line in sizes.report() {
            println!("  {line}");
        }
        // The statements up to the one on Tab concern Sections 2–6.
        let rows = sizes.rows();
        assert_eq!(rows[12].name, "Tab");
        for row in &rows[..13] {
            assert!(row.holds() && row.largest > 0, "{}", row.name);
        }
        // What Section 9 states for Section 7 follows: a cost is at most k entries of Tab, and
        // a cell sum is n^(k+1) costs.
        let cost = u128::from(k) * sizes.table;
        assert!(cost < 1 << 40);
        assert!(6_u128.pow(u32::from(k) + 1) * cost < 1 << 60);
    }

    #[test]
    fn the_sizes_of_section_9_for_five_gaps() {
        assert_section_9(5, (2, 1));
    }

    #[test]
    fn the_sizes_of_section_9_for_seven_gaps() {
        // The parameters of the largest spec file; only Sections 2–6 are carried out here.
        assert_section_9(7, (21, 10));
    }

    #[test]
    fn a_single_gap_cell() {
        // m = 1: the only cell is [0, ∞), its mass is 1, and a key is a number of gaps.
        let keys = Keys::new(1, 3);
        let params = Params {
            k: 3,
            h1: 2,
            h2: 1,
            mesh: 4,
            boundaries: Vec::new(),
            n: 2,
            nu: 1,
            tail: 3,
        };
        let tables = build(&params, &keys, &mut Sizes::default()).unwrap();
        assert_eq!(tables.masses, [D]);
        let table = &tables.table;
        assert_eq!(table.len(), 3 * 2);
        // More gaps, or a larger difference of the heights, make a segment longer. One gap is 1
        // on average, which is F in the units of the table; this fixes the scale of an entry.
        assert!(table[0] < table[2] && table[2] < table[4]);
        assert!((0..3).all(|rank| table[2 * rank] < table[2 * rank + 1]));
        assert!(u128::from(table[0]) > F && u128::from(table[0]) < 2 * F);
    }

    #[test]
    fn extreme_parameters_stop_cleanly() {
        let keys = Keys::new(2, 2);
        let mut sizes = Sizes::default();
        // A strip so high that the argument of ceil_sqrt would not fit in 128 bits.
        let high = params(2, (1 << 20, 1), 128, &[48]);
        assert!(matches!(
            build(&high, &keys, &mut sizes),
            Err(Stop::Invalid(_))
        ));
        // A boundary so far out that the tables would be too long.
        let far = params(2, (2, 1), 128, &[1 << 40]);
        assert!(matches!(
            build(&far, &keys, &mut sizes),
            Err(Stop::Invalid(_))
        ));
    }
}
