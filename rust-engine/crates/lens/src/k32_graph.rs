//! K_{3,2}^{(2)} graph — explicit vertex/edge/cell enumeration.
//!
//! Makes paper 1 capstone's topology uniqueness directly visible.
//! Cell counts match `chiral_dim(i,j) = C(NS,i)·C(NT,j)` and Euler:
//! `b_1 = E − V + 1 = 8 = NS² − 1 = 1/α_3`.
//!
//! Cites: TopologyCompare.K32_c2_b1, Paper1Chiral.chiralDim.

use crate::chiral_k32::{D, NS, NT};

const C_MULT: u64 = 2;

/// Vertex index in [0, D). S-side: [0, NS); T-side: [NS, D).
pub type Vertex = u8;
pub type Edge = (Vertex, Vertex, u8);

pub fn is_s(v: Vertex) -> bool { (v as u64) < NS }
pub fn is_t(v: Vertex) -> bool { (v as u64) >= NS && (v as u64) < D }

pub fn vertices() -> Vec<Vertex> { (0..D as u8).collect() }

pub fn edges() -> Vec<Edge> {
    let mut e = Vec::new();
    for s in 0..NS as u8 {
        for t in NS as u8..D as u8 {
            for k in 0..C_MULT as u8 { e.push((s, t, k)); }
        }
    }
    e
}

/// b_1 = E − V + 1. Lean: `TopologyCompare.K32_c2_b1`.
pub fn b1() -> u64 {
    edges().len() as u64 - vertices().len() as u64 + 1
}

fn subsets(n: u8, k: u32) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    if k as u64 > n as u64 { return out; }
    for mask in 0u32..(1u32 << n) {
        if mask.count_ones() == k {
            out.push((0..n).filter(|i| mask & (1u32 << i) != 0).collect());
        }
    }
    out
}

/// Chiral cells at level (i, j) — `len()` matches `chiral_dim(i,j)`.
pub fn chiral_cells(i: u32, j: u32) -> Vec<(Vec<u8>, Vec<u8>)> {
    let ss = subsets(NS as u8, i);
    let tt = subsets(NT as u8, j);
    let mut out = Vec::new();
    for s in &ss {
        for t in &tt {
            let t_abs: Vec<u8> = t.iter().map(|x| x + NS as u8).collect();
            out.push((s.clone(), t_abs));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chiral_k32::chiral_dim;

    #[test] fn five_vertices() { assert_eq!(vertices().len(), 5); }
    #[test] fn twelve_edges()  { assert_eq!(edges().len(), 12); }
    #[test] fn b1_is_eight()   { assert_eq!(b1(), 8); }

    #[test] fn cells_match_chiral_dim() {
        for i in 0..=3u32 { for j in 0..=2u32 {
            assert_eq!(chiral_cells(i, j).len() as u64,
                       chiral_dim(i as u64, j as u64));
        }}
    }
}
