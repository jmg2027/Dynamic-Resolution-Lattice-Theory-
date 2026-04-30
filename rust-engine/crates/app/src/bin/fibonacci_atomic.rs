//! `fibonacci-atomic` — (NS, NT, d) follow Fibonacci recurrence.
//! Lean: FibonacciAtomic.lean.
//!
//!   F_3 = 2  = NT
//!   F_4 = 3  = NS
//!   F_5 = 5  = d (= NS + NT, the recurrence!)
//!   F_6 = 8  = NS² − 1 = 1/α_3
//!   F_7 = 13 = NS² + NS + 1 = NH₃ denom
//!
//! → (NS, NT) is the unique consecutive Fibonacci pair such that
//!   d = next Fibonacci.  Forced by atomicity + canonical_partition.

fn fib(n: usize) -> u64 {
    let mut a = 0u64; let mut b = 1u64;
    for _ in 0..n { let t = a + b; a = b; b = t; }
    a
}

fn main() {
    println!("=== Fibonacci atomic — (NS, NT, d) = (F_4, F_3, F_5) ===\n");
    println!("  n   F_n     identification in DRLT");
    println!("─────────────────────────────────────────────────────");
    for n in 1..=10 {
        let f = fib(n);
        let id = match (n, f) {
            (3, 2)  => " = NT (chiral phase/time sector)",
            (4, 3)  => " = NS (chiral spatial sector)  ★",
            (5, 5)  => " = d  = NS + NT (recurrence!)",
            (6, 8)  => " = NS² − 1 = 1/α_3 (strong adjoint)",
            (7, 13) => " = NS² + NS + 1 = NH₃ denom",
            _ => "",
        };
        println!("  {}  {:>5}{}", n, f, id);
    }

    println!("\n★ Atomic forcing chain:");
    println!("  Atomicity → n=5 (unique alive decomp)");
    println!("  canonical_partition → (NS, NT) = (3, 2)");
    println!("  But 3, 2 are *consecutive Fibonacci F_4, F_3*");
    println!("  And 5 = 3 + 2 = F_5 (Fibonacci recurrence!)");
    println!("\n  → DRLT atoms are *forced to be consecutive Fibonacci*.");
    println!("  → 1/α_3 = NS²−1 = 8 = F_6 (next Fibonacci, not coincidence)");
    println!("  → NH₃ denom = NS²+NS+1 = 13 = F_7");

    println!("\n--- Golden ratio appears in CKM ---");
    println!("  φ = (1 + √5)/2 = lim F_{{n+1}}/F_n");
    println!("  CKM Wolfenstein A = φ/c (Lean CKMHierarchy.lean)");
    println!("  → DRLT lattice numerology = Fibonacci hierarchy");

    println!("\nLean cite: FibonacciAtomic (NS=F_4, NT=F_3, d=F_5)");
}
