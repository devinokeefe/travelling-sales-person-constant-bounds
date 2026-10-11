//! The largest values met during a run, for comparison with Section 9 of RECIPE.md.
//!
//! Nothing in the check depends on this record: the operations are guarded where they are
//! carried out, each on its own or by a bound that is checked before a loop. The record is
//! printed so that the bounds stated in Section 9 can be compared with what occurs. Section 9
//! states them for the spec files in `data/specs/` other than `rounding.txt`; for other
//! parameters a larger value is no error as long as it is below 2^128.

use crate::arith::bit_length;

/// The largest value of each kind of quantity that Section 9 bounds.
#[derive(Default)]
pub struct Sizes {
    /// Rup and Rlo.
    pub power: u128,
    /// The products of Section 2.
    pub power_product: u128,
    /// C_λ and C_μ.
    pub constant: u128,
    /// num_c(i).
    pub numerator: u128,
    /// W_c(i) and V_κ(s).
    pub weight: u128,
    /// P_c.
    pub mass: u128,
    /// The sums of Section 4.
    pub convolution: u128,
    /// (α·j)² + (γ·τ)².
    pub squares: u128,
    /// The argument of ceil_sqrt.
    pub root_argument: u128,
    /// Dist.
    pub distance: u128,
    /// The sums of Section 5.
    pub height_sum: u128,
    /// The sums of Section 6.
    pub table_sum: u128,
    /// Tab.
    pub table: u128,
    /// k times the largest entry of Tab, which is an upper bound for cost(g, a).
    pub cost: u128,
    /// k·max(Tab)·n^(k+1), which is an upper bound for S_g.
    pub cell_sum_bound: u128,
    /// S_g.
    pub cell_sum: u128,
    /// The sums of Section 8.
    pub total_sum: u128,
    /// The two sides of the final test.
    pub test_side: u128,
}

/// One statement of Section 9: the largest value met of a quantity, and the power of two that
/// bounds it for the spec files in `data/specs/` other than `rounding.txt`.
pub struct Row {
    pub name: &'static str,
    pub largest: u128,
    /// The bound is 2^`exponent`.
    pub exponent: u32,
    /// Whether the quantity is below the bound; otherwise it is at most the bound.
    pub strict: bool,
}

impl Row {
    /// Whether the largest value met respects the bound.
    pub fn holds(&self) -> bool {
        let bound = 1 << self.exponent;
        self.largest < bound || (!self.strict && self.largest == bound)
    }
}

impl Sizes {
    /// The statements of Section 9, in the order of the sections in which the quantities occur.
    pub fn rows(&self) -> Vec<Row> {
        let row = |name, largest, exponent, strict| Row {
            name,
            largest,
            exponent,
            strict,
        };
        vec![
            row("Rup, Rlo", self.power, 62, false),
            row("products in Section 2", self.power_product, 124, true),
            row("C_λ, C_μ", self.constant, 57, true),
            row("num_c(i)", self.numerator, 120, true),
            row("W_c(i), V_κ(s)", self.weight, 45, true),
            row("P_c", self.mass, 48, false),
            row("sums in Section 4", self.convolution, 93, true),
            row("(α·j)² + (γ·τ)²", self.squares, 59, true),
            row("argument of ceil_sqrt", self.root_argument, 123, true),
            row("Dist", self.distance, 40, true),
            row("sums in Section 5", self.height_sum, 56, true),
            row("sums in Section 6", self.table_sum, 85, true),
            row("Tab", self.table, 37, true),
            row("k·max(Tab), a bound for cost", self.cost, 40, true),
            row("k·max(Tab)·n^(k+1)", self.cell_sum_bound, 66, true),
            row("S_g", self.cell_sum, 63, true),
            row("sums in Section 8", self.total_sum, 111, true),
            row("sides of the final test", self.test_side, 78, true),
        ]
    }

    /// One line for each statement: the number of binary digits of the largest value met, the
    /// bound of Section 9, and a remark if the value is larger in this run.
    pub fn report(&self) -> Vec<String> {
        self.rows()
            .iter()
            .map(|row| {
                let digits = bit_length(row.largest);
                let relation = if row.strict { "below" } else { "at most" };
                let remark = if row.holds() {
                    ""
                } else {
                    ": larger in this run"
                };
                format!(
                    "{}: {digits} binary digits; Section 9: {relation} 2^{}{remark}",
                    row.name, row.exponent
                )
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_bound_is_strict_or_not() {
        let sizes = Sizes {
            power: 1 << 62,
            power_product: 1 << 124,
            mass: (1 << 48) + 1,
            ..Sizes::default()
        };
        let rows = sizes.rows();
        assert!(rows[0].holds() && !rows[1].holds() && !rows[5].holds());
        assert!(rows[2..5].iter().chain(&rows[6..]).all(Row::holds));
        let report = sizes.report();
        assert_eq!(
            report[0],
            "Rup, Rlo: 63 binary digits; Section 9: at most 2^62"
        );
        assert_eq!(
            report[1],
            "products in Section 2: 125 binary digits; Section 9: below 2^124: larger in this run"
        );
        assert_eq!(report.len(), 18);
    }
}
