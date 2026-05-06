//! K_{3,2}^{(2)} fundamental cycle basis (b_1 = 8).
//!
//! Builds a spanning tree by union-find then computes the unique
//! tree path for each non-tree edge.  Each non-tree edge + its
//! tree-path closure = one fundamental cycle.  Total = b_1 = 8.

use crate::chiral_k32::D;
use crate::k32_graph::{edges, vertices};
use std::collections::VecDeque;

/// (spanning tree edge indices, non-tree edge indices).
pub fn spanning_tree_split() -> (Vec<usize>, Vec<usize>) {
    let n = D as usize;
    let mut p: Vec<usize> = (0..n).collect();
    fn root(p: &mut [usize], mut x: usize) -> usize {
        while p[x] != x { p[x] = p[p[x]]; x = p[x]; } x
    }
    let (mut tree, mut cobase) = (Vec::new(), Vec::new());
    for (i, &(s, t, _)) in edges().iter().enumerate() {
        let (rs, rt) = (root(&mut p, s as usize), root(&mut p, t as usize));
        if rs != rt { p[rs] = rt; tree.push(i); } else { cobase.push(i); }
    }
    (tree, cobase)
}

/// 8 fundamental cycles of K_{3,2}^{(2)} as edge-index lists.
pub fn cycle_basis() -> Vec<Vec<usize>> {
    let (tree, cobase) = spanning_tree_split();
    let elist = edges();
    let n = vertices().len();
    let mut adj: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n];
    for &i in &tree {
        let (s, t, _) = elist[i];
        adj[s as usize].push((t as usize, i));
        adj[t as usize].push((s as usize, i));
    }
    let path = |start: usize, end: usize| -> Vec<usize> {
        let mut par = vec![(usize::MAX, usize::MAX); n];
        par[start] = (start, usize::MAX);
        let mut q: VecDeque<usize> = VecDeque::from([start]);
        while let Some(v) = q.pop_front() {
            if v == end { break; }
            for &(u, e) in &adj[v] {
                if par[u].0 == usize::MAX && u != start {
                    par[u] = (v, e); q.push_back(u);
                }
            }
        }
        let (mut out, mut c) = (Vec::new(), end);
        while c != start { out.push(par[c].1); c = par[c].0; }
        out
    };
    cobase.iter().map(|&i| {
        let (s, t, _) = elist[i];
        let mut cy = vec![i];
        cy.extend(path(t as usize, s as usize));
        cy
    }).collect()
}

/// Histogram of cycle lengths in the basis.
pub fn cycle_length_distribution() -> Vec<(usize, usize)> {
    let mut counts = std::collections::BTreeMap::new();
    for c in cycle_basis() { *counts.entry(c.len()).or_insert(0) += 1; }
    counts.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn basis_size_is_b1() { assert_eq!(cycle_basis().len(), 8); }
    #[test] fn tree_plus_cobase_eq_edges() {
        let (t, c) = spanning_tree_split();
        assert_eq!(t.len() + c.len(), edges().len());
        assert_eq!(t.len(), 4);
        assert_eq!(c.len(), 8);
    }
}
