//! `k32-inspect` — explicit visualization of K_{3,2}^{(2)}.
//!
//! Prints all 5 vertices, 12 edges, and 32 chiral cells across
//! levels (i, j) with i ∈ [0, 3], j ∈ [0, 2].

use drlt_hypervisor::chiral_k32::chiral_dim;
use drlt_hypervisor::k32_cycles::{cycle_basis, cycle_length_distribution};
use drlt_hypervisor::k32_graph::{b1, chiral_cells, edges, is_s, vertices, Vertex};

fn name(v: Vertex) -> String {
    if is_s(v) { format!("s_{}", v) } else { format!("t_{}", v - 3) }
}

fn main() {
    println!("=== K_{{3,2}}^{{(2)}} graph (explicit enumeration) ===\n");

    let vs = vertices();
    print!("Vertices ({}): ", vs.len());
    for v in &vs { print!("{} ", name(*v)); }
    println!("\n");

    println!("Edges ({}, S → T, multiplicity c=2):", edges().len());
    for (s, t, k) in edges() {
        println!("  {} ──[{}]── {}", name(s), k, name(t));
    }
    println!();

    println!("b_1 = E − V + 1 = {} − {} + 1 = {}",
        edges().len(), vs.len(), b1());
    println!("    = NS² − 1 = 8 = 1/α_3   (paper 2 result)\n");

    println!("=== Chiral cells (level (i, j), i ≤ NS=3, j ≤ NT=2) ===");
    let mut total = 0u64;
    for i in 0..=3u32 {
        for j in 0..=2u32 {
            let cells = chiral_cells(i, j);
            let n = cells.len() as u64;
            total += n;
            print!("  ({},{}) → {:2} cells   [chiralDim = {:2}]   ",
                i, j, n, chiral_dim(i as u64, j as u64));
            for (idx, (s, t)) in cells.iter().take(3).enumerate() {
                if idx > 0 { print!(", "); }
                let names: Vec<_> = s.iter().chain(t.iter())
                    .map(|&x| name(x)).collect();
                print!("{{{}}}", names.join(","));
            }
            if cells.len() > 3 { print!(", ..."); }
            println!();
        }
    }
    println!("\nTotal cells across all levels: {} = 2^d = {}",
        total, 1u64 << 5);

    println!("\n=== Cycle basis (b_1 = {} fundamental cycles) ===", b1());
    let elist = edges();
    for (i, cy) in cycle_basis().iter().enumerate() {
        print!("  cycle {} (len {}):", i + 1, cy.len());
        for &e in cy {
            let (s, t, k) = elist[e];
            print!("  {}-{}[{}]", name(s), name(t), k);
        }
        println!();
    }
    println!("\nLength distribution: {:?}",
        cycle_length_distribution());
    let total_len: usize = cycle_basis().iter().map(|c| c.len()).sum();
    println!("Sum of lengths: {} = 2·E - 2·tree = 2·8 + ... structural", total_len);
}
