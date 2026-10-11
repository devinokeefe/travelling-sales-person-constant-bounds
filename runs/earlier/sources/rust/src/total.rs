//! Section 8 of RECIPE.md: the total and the test.

use crate::arith::{add, ceil_div, mul, power, raise, wide};
use crate::failure::{invalid, Outcome};
use crate::files::Params;
use crate::sizes::Sizes;
use crate::tables::{D, F};

/// The total `A_0`, from the masses `P_c` and the cell sums `S_g` in index order.
pub fn total(masses: &[u128], sums: &[u128], k: usize, sizes: &mut Sizes) -> Outcome<u128> {
    let cells = masses.len();
    if wide(sums.len()) != power(wide(cells), k, "m^k")? {
        return invalid("internal error: wrong number of cell sums".to_string());
    }
    // `level` holds A_j in the index order g_1 + g_2·m + … + g_j·m^(j−1), so the tuples that
    // differ only in g_j are m^(j−1) places apart.
    let mut level = sums.to_vec();
    for _ in 0..k {
        let shorter = level.len() / cells;
        let mut next = Vec::with_capacity(shorter);
        for index in 0..shorter {
            let mut sum = 0;
            for (c, &mass) in masses.iter().enumerate() {
                let term = mul(mass, level[index + c * shorter], "P_c·A_j")?;
                sum = add(sum, term, "a sum in Section 8")?;
            }
            raise(&mut sizes.total_sum, sum);
            next.push(ceil_div(sum, D, "A_j")?);
        }
        level = next;
    }
    Ok(level[0])
}

/// The outcome of the test of Section 8.
pub struct Verdict {
    /// ceil(B·10^12): the bound with its first 12 decimals, rounded up.
    pub decimals: u128,
    /// Whether B ≤ θ.
    pub accepted: bool,
}

/// Compares the bound B = `A_0`·h_2 / (n^(k+1)·F·k·h_1) with the threshold θ_1/θ_2.
pub fn test(
    total: u128,
    params: &Params,
    threshold: (u64, u64),
    sizes: &mut Sizes,
) -> Outcome<Verdict> {
    let (theta_1, theta_2) = (u128::from(threshold.0), u128::from(threshold.1));
    let numerator = mul(total, u128::from(params.h2), "A_0·h_2")?;
    let mut denominator = power(wide(params.n), params.k + 1, "n^(k+1)")?;
    for factor in [F, wide(params.k), u128::from(params.h1)] {
        denominator = mul(denominator, factor, "n^(k+1)·F·k·h_1")?;
    }
    let left = mul(numerator, theta_2, "A_0·h_2·θ_2")?;
    let right = mul(theta_1, denominator, "θ_1·n^(k+1)·F·k·h_1")?;
    raise(&mut sizes.test_side, left.max(right));

    let scaled = mul(numerator, 1_000_000_000_000, "A_0·h_2·10^12")?;
    Ok(Verdict {
        decimals: ceil_div(scaled, denominator, "the bound")?,
        accepted: left <= right,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_total_folds_the_last_gap_first() {
        let mut sizes = Sizes::default();
        // m = 2, k = 2 with masses D and 2D: A_1(g_1) = S(g_1, 0) + 2·S(g_1, 1).
        let masses = [D, 2 * D];
        let sums = [1, 10, 100, 1000];
        // A_1(0) = 1 + 200, A_1(1) = 10 + 2000, A_0 = 201 + 2·2010.
        assert_eq!(total(&masses, &sums, 2, &mut sizes).unwrap(), 4221);
        assert_eq!(sizes.total_sum, 4221 * D);
        // Every step rounds up: ceil(1·3/D) = 1 and ceil(1·1/D) = 1.
        assert_eq!(total(&[1], &[3], 2, &mut sizes).unwrap(), 1);
        assert_eq!(total(&[D - 1], &[D], 1, &mut sizes).unwrap(), D - 1);
        assert_eq!(total(&[D + 1], &[D + 1], 1, &mut sizes).unwrap(), D + 3);
        assert!(total(&masses, &sums[..3], 2, &mut sizes).is_err());
    }

    #[test]
    fn the_test_compares_exactly() {
        let params = Params {
            k: 2,
            h1: 3,
            h2: 2,
            mesh: 2,
            boundaries: Vec::new(),
            n: 2,
            nu: 1,
            tail: 1,
        };
        let mut sizes = Sizes::default();
        // The denominator is 2^3·F·2·3 = 48·F, so that B = A_0/(24·F).
        let total = 18 * F;
        let exact = test(total, &params, (3, 4), &mut sizes).unwrap();
        assert!(exact.accepted);
        assert_eq!(exact.decimals, 750_000_000_000);
        // One unit of A_0 is 10^12/(24·F) = 9.70… units of the twelfth decimal.
        let above = test(total + 1, &params, (3, 4), &mut sizes).unwrap();
        assert!(!above.accepted);
        assert_eq!(above.decimals, 750_000_000_010);
        let below = test(total - 1, &params, (3, 4), &mut sizes).unwrap();
        assert!(below.accepted);
        assert_eq!(below.decimals, 749_999_999_991);
        assert_eq!(
            test(48 * F, &params, (2, 1), &mut sizes).unwrap().decimals,
            2_000_000_000_000
        );
        assert!(test(u128::MAX, &params, (3, 4), &mut sizes).is_err());
    }
}
