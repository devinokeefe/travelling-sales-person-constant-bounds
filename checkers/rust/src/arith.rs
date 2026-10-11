//! Checked integer arithmetic.
//!
//! Every quantity of the recipe is a non-negative integer. For the spec files in `data/specs/`
//! all of them are below 2^124; for other parameters that a spec file may have, some exceed
//! 2^128 (RECIPE.md, Section 9). So `u128` is used, and the helpers here return an error instead
//! of wrapping; the caller names the quantity, so that the message says which bound failed.

use crate::failure::{Outcome, Stop};

/// A table that this program computes is refused if it would have more entries than this (the
/// two lists of Section 2 may have one more). The recipe sets no such limit. It bounds the
/// memory that a spec file can ask for; it does not exclude that memory runs out.
pub const MAX_ENTRIES: u128 = 1 << 27;

fn violated(what: &str, how: &str) -> Stop {
    Stop::Invalid(format!("arithmetic bound violated: {what} {how}"))
}

/// `a + b`.
pub fn add(a: u128, b: u128, what: &str) -> Outcome<u128> {
    a.checked_add(b)
        .ok_or_else(|| violated(what, "does not fit in 128 bits"))
}

/// `a − b`, which must not be negative.
pub fn sub(a: u128, b: u128, what: &str) -> Outcome<u128> {
    a.checked_sub(b)
        .ok_or_else(|| violated(what, "is negative"))
}

/// `a · b`.
pub fn mul(a: u128, b: u128, what: &str) -> Outcome<u128> {
    a.checked_mul(b)
        .ok_or_else(|| violated(what, "does not fit in 128 bits"))
}

/// `base^exponent`.
pub fn power(base: u128, exponent: usize, what: &str) -> Outcome<u128> {
    let mut result = 1;
    for _ in 0..exponent {
        result = mul(result, base, what)?;
    }
    Ok(result)
}

/// `floor(a / b)`.
pub fn floor_div(a: u128, b: u128, what: &str) -> Outcome<u128> {
    a.checked_div(b)
        .ok_or_else(|| violated(what, "has the divisor zero"))
}

/// `ceil(a / b)`. In several places, where the divisor is a constant, the standard `div_ceil` is
/// used instead; it computes the same.
pub fn ceil_div(a: u128, b: u128, what: &str) -> Outcome<u128> {
    let quotient = floor_div(a, b, what)?;
    // A non-zero remainder needs b ≥ 2; then the quotient is at most a/2 and one can be added.
    Ok(if a.is_multiple_of(b) {
        quotient
    } else {
        quotient + 1
    })
}

/// The largest integer `r` with `r² ≤ a`.
pub fn floor_sqrt(a: u128) -> u128 {
    if a < 2 {
        return a;
    }
    // Newton's iteration x → floor((x + floor(a/x)) / 2). If x ≥ floor(√a) then so is the next
    // value (inequality of the arithmetic and geometric means), and if x > floor(√a) then
    // floor(a/x) < x, so the next value is smaller. Started at a power of two above √a, the
    // iteration therefore decreases strictly until it reaches floor(√a), where it stops.
    let bits = u128::BITS - a.leading_zeros();
    let mut x = 1_u128 << bits.div_ceil(2);
    loop {
        let next = u128::midpoint(x, a / x);
        if next >= x {
            return x;
        }
        x = next;
    }
}

/// The least integer `u ≥ 0` with `u² ≥ a` (RECIPE.md, preamble).
pub fn ceil_sqrt(a: u128) -> u128 {
    let root = floor_sqrt(a);
    // root ≤ 2^64 − 1, so neither the square nor root + 1 can overflow.
    if root * root == a {
        root
    } else {
        root + 1
    }
}

/// The greatest common divisor.
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The number of binary digits of `a`: the least `e` with `a < 2^e`.
pub fn bit_length(a: u128) -> u32 {
    u128::BITS - a.leading_zeros()
}

/// A count or an index as a wide integer.
pub fn wide(count: usize) -> u128 {
    // Lossless: `usize` has at most 64 bits on every platform that Rust supports.
    count as u128
}

/// A value that the recipe keeps below 2^64, as a 64-bit integer.
pub fn narrow(a: u128, what: &str) -> Outcome<u64> {
    u64::try_from(a).map_err(|_| violated(what, "does not fit in 64 bits"))
}

/// A table length or an index into a table.
pub fn length(a: u128, what: &str) -> Outcome<usize> {
    if a > MAX_ENTRIES {
        return Err(Stop::Invalid(format!(
            "{what} is {a}, more than this program allows ({MAX_ENTRIES})"
        )));
    }
    usize::try_from(a).map_err(|_| violated(what, "does not fit in a machine word"))
}

/// Replaces `*largest` by `value` if that is larger; used to record the sizes of Section 9.
pub fn raise(largest: &mut u128, value: u128) {
    if value > *largest {
        *largest = value;
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    /// The pseudo-random numbers of the tests: the `SplitMix64` sequence with a fixed seed.
    pub struct Random(pub u64);

    impl Random {
        pub fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        pub fn below(&mut self, bound: u64) -> u64 {
            self.next() % bound
        }

        pub fn wide(&mut self) -> u128 {
            (u128::from(self.next()) << 64) | u128::from(self.next())
        }
    }

    #[test]
    fn ceil_div_rounds_up() {
        assert_eq!(ceil_div(0, 7, "x").unwrap(), 0);
        assert_eq!(ceil_div(1, 7, "x").unwrap(), 1);
        assert_eq!(ceil_div(6, 7, "x").unwrap(), 1);
        assert_eq!(ceil_div(7, 7, "x").unwrap(), 1);
        assert_eq!(ceil_div(8, 7, "x").unwrap(), 2);
        assert_eq!(ceil_div(14, 7, "x").unwrap(), 2);
        assert_eq!(ceil_div(15, 1, "x").unwrap(), 15);
        assert_eq!(ceil_div(u128::MAX, 1, "x").unwrap(), u128::MAX);
        assert_eq!(ceil_div(u128::MAX, 2, "x").unwrap(), 1 << 127);
        assert_eq!(ceil_div(u128::MAX, u128::MAX, "x").unwrap(), 1);
        assert_eq!(ceil_div(u128::MAX - 1, u128::MAX, "x").unwrap(), 1);
        assert_eq!(
            ceil_div((1 << 124) + 1, 1 << 62, "x").unwrap(),
            (1 << 62) + 1
        );
        assert_eq!(floor_div((1 << 124) + 1, 1 << 62, "x").unwrap(), 1 << 62);
    }

    #[test]
    fn ceil_div_is_the_least_multiple_count() {
        let mut random = Random(1);
        for _ in 0..20_000 {
            let a = random.wide() >> random.below(128);
            let b = (random.wide() >> random.below(128)).max(1);
            let q = ceil_div(a, b, "x").unwrap();
            assert_eq!(q, a.div_ceil(b));
            // q is the least integer with q·b ≥ a.
            assert!(q.checked_mul(b).is_none_or(|product| product >= a));
            assert!(q == 0 || (q - 1) * b < a);
        }
    }

    #[test]
    fn division_by_zero_and_overflow_are_reported() {
        assert!(ceil_div(1, 0, "x").is_err());
        assert!(floor_div(1, 0, "x").is_err());
        assert!(add(u128::MAX, 1, "x").is_err());
        assert!(sub(1, 2, "x").is_err());
        assert!(mul(1 << 64, 1 << 64, "x").is_err());
        assert_eq!(mul((1 << 64) - 1, 1 << 64, "x").unwrap(), u128::MAX << 64);
        assert!(power(2, 128, "x").is_err());
        assert_eq!(power(2, 127, "x").unwrap(), 1 << 127);
        assert_eq!(power(6, 8, "x").unwrap(), 1_679_616);
        assert!(narrow(1 << 64, "x").is_err());
        assert_eq!(narrow((1 << 64) - 1, "x").unwrap(), u64::MAX);
        assert!(length(MAX_ENTRIES + 1, "x").is_err());
    }

    /// Checks the definition: u² ≥ a, and (u − 1)² < a unless u = 0.
    fn assert_ceil_sqrt(a: u128) {
        let u = ceil_sqrt(a);
        assert!(u.checked_mul(u).is_none_or(|square| square >= a), "{a}");
        assert!(u == 0 || (u - 1) * (u - 1) < a, "{a}");
    }

    #[test]
    fn ceil_sqrt_at_squares_and_their_neighbours() {
        assert_eq!(ceil_sqrt(0), 0);
        assert_eq!(ceil_sqrt(1), 1);
        assert_eq!(ceil_sqrt(2), 2);
        assert_eq!(ceil_sqrt(3), 2);
        assert_eq!(ceil_sqrt(4), 2);
        assert_eq!(ceil_sqrt(5), 3);
        let mut roots: Vec<u128> = (2..2000).collect();
        for exponent in 11..=64 {
            let power = 1_u128 << exponent;
            roots.extend([power - 2, power - 1]);
            if exponent < 64 {
                roots.extend([power, power + 1, power + 2]);
            }
        }
        let mut random = Random(2);
        for _ in 0..5000 {
            roots.push(u128::from(random.next() >> random.below(63)).max(2));
        }
        for r in roots {
            assert_eq!(ceil_sqrt(r * r), r);
            assert_eq!(ceil_sqrt(r * r - 1), r);
            assert_eq!(ceil_sqrt(r * r + 1), r + 1);
            assert_eq!(floor_sqrt(r * r - 1), r - 1);
            assert_eq!(floor_sqrt(r * r), r);
            assert_eq!(floor_sqrt(r * r + 1), r);
        }
    }

    #[test]
    fn ceil_sqrt_near_two_to_the_124_and_at_the_top() {
        let big = 1_u128 << 124;
        assert_eq!(ceil_sqrt(big), 1 << 62);
        assert_eq!(ceil_sqrt(big - 1), 1 << 62);
        assert_eq!(ceil_sqrt(big + 1), (1 << 62) + 1);
        // (2^62 − 1)² = 2^124 − 2^63 + 1.
        assert_eq!(ceil_sqrt(big - (1 << 63) + 1), (1 << 62) - 1);
        assert_eq!(ceil_sqrt(big - (1 << 63) + 2), 1 << 62);
        assert_eq!(ceil_sqrt(big - (1 << 63)), (1 << 62) - 1);
        // (2^62 + 1)² = 2^124 + 2^63 + 1.
        assert_eq!(ceil_sqrt(big + (1 << 63) + 1), (1 << 62) + 1);
        assert_eq!(ceil_sqrt(big + (1 << 63) + 2), (1 << 62) + 2);
        assert_eq!(ceil_sqrt(u128::MAX), 1 << 64);
        assert_eq!(floor_sqrt(u128::MAX), (1 << 64) - 1);
        // (2^64 − 1)² = 2^128 − 2^65 + 1.
        assert_eq!(ceil_sqrt(u128::MAX - (1 << 65) + 2), (1 << 64) - 1);
        assert_eq!(ceil_sqrt(u128::MAX - (1 << 65) + 3), 1 << 64);
        let mut random = Random(3);
        for _ in 0..20_000 {
            let offset = u128::from(random.next());
            assert_ceil_sqrt(big + offset);
            assert_ceil_sqrt(big - offset);
            assert_ceil_sqrt(random.wide() >> random.below(128));
        }
    }

    #[test]
    fn gcd_and_bit_length() {
        assert_eq!(gcd(21, 10), 1);
        assert_eq!(gcd(42, 10), 2);
        assert_eq!(gcd(0, 5), 5);
        assert_eq!(gcd(5, 0), 5);
        assert_eq!(gcd(1 << 40, 1 << 20), 1 << 20);
        assert_eq!(bit_length(0), 0);
        assert_eq!(bit_length(1), 1);
        assert_eq!(bit_length((1 << 62) - 1), 62);
        assert_eq!(bit_length(1 << 62), 63);
        assert_eq!(bit_length(u128::MAX), 128);
    }
}
