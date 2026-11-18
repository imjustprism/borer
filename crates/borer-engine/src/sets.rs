//! A disjoint-set forest over `0..n`, with path halving and the smaller
//! root kept, so its roots do not depend on the order of the joins.

/// A disjoint-set forest over `0..n`.
#[derive(Debug)]
pub(crate) struct Sets {
    /// Each element's parent.
    parent: Vec<usize>,
}

impl Sets {
    /// Returns a forest of `n` single elements.
    ///
    /// # Arguments
    ///
    /// * `n` - How many elements.
    pub(crate) fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
        }
    }

    /// Returns the root of an element's set.
    ///
    /// # Arguments
    ///
    /// * `x` - The element.
    pub(crate) fn find(&mut self, mut x: usize) -> usize {
        while let Some(&p) = self.parent.get(x) {
            if p == x {
                break;
            }
            let gp = self.parent.get(p).copied().unwrap_or(p);
            if let Some(slot) = self.parent.get_mut(x) {
                *slot = gp;
            }
            x = gp;
        }
        x
    }

    /// Joins two elements' sets under the smaller root.
    ///
    /// # Arguments
    ///
    /// * `a` - One element.
    /// * `b` - The other.
    pub(crate) fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        let (lo, hi) = (ra.min(rb), ra.max(rb));
        if let Some(slot) = self.parent.get_mut(hi) {
            *slot = lo;
        }
    }
}
