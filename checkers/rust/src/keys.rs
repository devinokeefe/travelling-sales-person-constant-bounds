//! Keys (RECIPE.md, Section 4).
//!
//! A key κ = (κ_0, …, κ_{m−1}) records how many gaps of each cell lie between the two ends of a
//! segment; its entries are non-negative and their sum is between 1 and k.

/// The largest number of gap cells that a spec file may ask for.
pub const MAX_CELLS: usize = 8;

/// A key. The entries beyond the number of cells are zero, so that the order of the arrays is
/// the lexicographic order of the vectors.
pub type Key = [u8; MAX_CELLS];

/// All keys for given m and k, in the order of Section 4.
pub struct Keys {
    list: Vec<Key>,
}

impl Keys {
    /// Lists the keys for `cells` gap cells (at most `MAX_CELLS`) and blocks of `gaps` gaps.
    pub fn new(cells: usize, gaps: u8) -> Self {
        let mut list = Vec::new();
        extend(&mut [0; MAX_CELLS], 0, cells, gaps, &mut list);
        Self { list }
    }

    /// The number of keys.
    pub fn len(&self) -> usize {
        self.list.len()
    }

    /// The keys in order.
    pub fn iter(&self) -> std::slice::Iter<'_, Key> {
        self.list.iter()
    }

    /// The position of `key` in the order, counted from 0.
    pub fn rank(&self, key: Key) -> Option<usize> {
        self.list.binary_search(&key).ok()
    }
}

/// Appends all keys that agree with `key` before position `cell` and whose further entries add
/// up to at most `left`. Smaller entries come first, which gives the lexicographic order.
fn extend(key: &mut Key, cell: usize, cells: usize, left: u8, list: &mut Vec<Key>) {
    if cell == cells {
        // The zero vector is not a key.
        if key.iter().any(|&count| count > 0) {
            list.push(*key);
        }
        return;
    }
    for count in 0..=left {
        key[cell] = count;
        extend(key, cell + 1, cells, left - count, list);
    }
    key[cell] = 0;
}

/// The number of gaps that a key counts.
pub fn gaps_of(key: Key) -> usize {
    key.iter().map(|&count| usize::from(count)).sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The binomial coefficient C(n, r).
    fn binomial(n: usize, r: usize) -> usize {
        (0..r).fold(1, |value, i| value * (n - i) / (i + 1))
    }

    /// The rank by counting: the vectors below κ in the lexicographic order are those that agree
    /// with κ before some position c and have a smaller entry v there; the entries after c are
    /// then free, with sum at most the rest r, which gives C(m − c − 1 + r, r) vectors. One of
    /// the vectors below κ is the zero vector, which is not a key.
    fn rank_by_counting(key: Key, cells: usize, gaps: usize) -> usize {
        let mut below = 0;
        let mut used = 0;
        for (c, &count) in key.iter().enumerate().take(cells) {
            for v in 0..usize::from(count) {
                let rest = gaps - used - v;
                below += binomial(cells - c - 1 + rest, rest);
            }
            used += usize::from(count);
        }
        below - 1
    }

    #[test]
    fn count_order_and_rank() {
        for cells in 1..=MAX_CELLS {
            for gaps in 2..=9_u8 {
                let k = usize::from(gaps);
                let keys = Keys::new(cells, gaps);
                assert_eq!(keys.len(), binomial(cells + k, k) - 1);
                for (rank, key) in keys.iter().enumerate() {
                    assert!((1..=k).contains(&gaps_of(*key)));
                    assert!(key[cells..].iter().all(|&count| count == 0));
                    assert_eq!(keys.rank(*key), Some(rank));
                    assert_eq!(rank_by_counting(*key, cells, k), rank);
                }
                for pair in keys.list.windows(2) {
                    let first = pair[0].iter().zip(&pair[1]).position(|(a, b)| a != b);
                    let c = first.expect("two keys are equal");
                    assert!(pair[0][c] < pair[1][c]);
                }
            }
        }
    }

    #[test]
    fn the_keys_of_the_small_example() {
        // m = 3, k = 3: the 19 keys in the order of the values file of the small example.
        let keys = Keys::new(3, 3);
        let expected: [[u8; 3]; 19] = [
            [0, 0, 1],
            [0, 0, 2],
            [0, 0, 3],
            [0, 1, 0],
            [0, 1, 1],
            [0, 1, 2],
            [0, 2, 0],
            [0, 2, 1],
            [0, 3, 0],
            [1, 0, 0],
            [1, 0, 1],
            [1, 0, 2],
            [1, 1, 0],
            [1, 1, 1],
            [1, 2, 0],
            [2, 0, 0],
            [2, 0, 1],
            [2, 1, 0],
            [3, 0, 0],
        ];
        assert_eq!(keys.len(), expected.len());
        for (key, want) in keys.iter().zip(expected) {
            assert_eq!(key[..3], want);
        }
        assert_eq!(keys.rank([0; MAX_CELLS]), None);
        assert_eq!(keys.rank([2, 2, 0, 0, 0, 0, 0, 0]), None);
    }
}
