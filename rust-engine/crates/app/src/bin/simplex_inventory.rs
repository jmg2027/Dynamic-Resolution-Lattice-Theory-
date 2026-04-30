//! `simplex-inventory` — exhaustive enumeration of the 31 non-empty
//! sub-simplices of the (3+2)-partitioned 4-simplex, organised by
//! chirality class (i, j) = (# A-vertices, # B-vertices).
//!
//! User insight (2026-04): each sub-simplex is a "geometric impedance"
//! channel; their *total* contributes to 1/α_em(IR).  The 5-term
//! formula already accounts for some classes — this tool surfaces
//! which classes are mapped vs unaccounted, making the "missing
//! correction" search structural rather than numerical.

use drlt_hypervisor::chiral_k32::chiral_dim;

const NS: u64 = 3;
const NT: u64 = 2;
const D:  u64 = 5;

fn label(i: u64, j: u64) -> &'static str {
    match (i, j) {
        (0, 0) => "(empty)",
        (1, 0) => "A-vertex",
        (0, 1) => "B-vertex",
        (2, 0) => "A-A edge",
        (1, 1) => "A-B edge",
        (0, 2) => "B-B edge",
        (3, 0) => "AAA triangle",
        (2, 1) => "AAB triangle",
        (1, 2) => "ABB triangle",
        (3, 1) => "AAAB tetrahedron",
        (2, 2) => "AABB tetrahedron",
        (3, 2) => "AAABB hypercell",
        _      => "(impossible)",
    }
}

fn main() {
    println!("=== K_{{3,2}}^{{(c=2)}} sub-simplex inventory ===");
    println!("(per user 2026-04: 31 = 2^d − 1 sub-simplices)\n");
    println!("| (i,j) | count | dim | type                |");
    println!("|-------|-------|-----|---------------------|");

    let mut total = 0u64;
    let mut per_dim: [u64; 6] = [0; 6];
    for k in 0..=(NS + NT) {
        for i in 0..=NS {
            if i > k { continue; }
            let j = k - i;
            if j > NT { continue; }
            let n = chiral_dim(i, j);
            if n == 0 { continue; }
            let dim_simplex = if i + j == 0 { -1i32 } else { (i + j) as i32 - 1 };
            println!("| ({},{}) | {:5} | {:3} | {:<19} |",
                i, j, n, dim_simplex, label(i, j));
            total += n;
            if i + j > 0 { per_dim[(i + j - 1) as usize] += n; }
        }
    }
    println!("|-------|-------|-----|---------------------|");
    println!("| total non-empty: {} = 2^d − 1 = {}",
        total - 1, (1u64 << D) - 1);
    println!("| total all:       {} = 2^d     = {}",
        total, 1u64 << D);

    println!("\nPer-simplex-dimension totals (= C(d, k+1)):");
    for k in 0..5 {
        if per_dim[k] == 0 { continue; }
        println!("  dim {}: {:2}  = C({}, {}) ", k, per_dim[k], D, k + 1);
    }

    println!("\n=== Current 5-term attribution (where mapped) ===");
    println!("60·ζ(2)        ←  c·count(1,1)·d = 2·6·5 = 60   [A-B edges, mult]");
    println!("30             ←  ?  candidate: NS·C(d,3) = 3·10 = 30");
    println!("25/3           ←  d²/NS  (block-pair partition, distinct framework)");
    println!("α_GUT/(NS+1)   ←  ?  Dyson tail with face-dim denominator");
    println!("α_GUT/(NS²·d)  ←  ?  proposed (gap candidate)");
    println!();
    println!("Unaccounted classes: A-A edges (3), B-B edges (1),");
    println!("triangles (10), tetrahedra (5), hypercell (1) — 20 of 31.");
    println!("Each could contribute a small impedance C_(i,j) to 1/α_em.");
}
