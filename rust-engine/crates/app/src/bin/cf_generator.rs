//! `cf-generator` — continued fraction expansions of 213 couplings
//! vs null-hypothesis irrationals.  CF via Euclidean algorithm.
//! Marks lattice integers {2, 3, 5, 8, 9, 10, 12, 25, 30, 45, 60}.

use drlt_app::basel::{s_partial, upper};
use drlt_app::gap_explorer::nat;
use num_bigint::BigUint;

fn cf(mut p: BigUint, mut q: BigUint, max: usize) -> Vec<BigUint> {
    let zero = BigUint::from(0u32);
    let mut out = Vec::new();
    while q != zero && out.len() < max {
        out.push(&p / &q);
        let r = &p % &q;
        p = q; q = r;
    }
    out
}

const LATTICE: &[u64] = &[2, 3, 5, 8, 9, 10, 12, 25, 30, 45, 60];

fn fmt(coeffs: &[BigUint]) -> String {
    let mut s = String::from("[");
    for (i, c) in coeffs.iter().enumerate() {
        let v = c.to_string();
        let n = v.parse::<u64>().unwrap_or(u64::MAX);
        let mark = if LATTICE.contains(&n) { "★" } else { "" };
        if i == 0 { s += &format!("{v}{mark}; "); }
        else { s += &format!("{v}{mark}{}", if i+1 == coeffs.len() {""} else {", "}); }
    }
    s + "]"
}

fn show(label: &str, p: BigUint, q: BigUint) {
    println!("  {:<22} {}", label, fmt(&cf(p, q, 12)));
}

fn main() {
    let s = s_partial(2000); let u = upper(2000);
    println!("=== Continued fraction expansions ===");
    println!("  ★ marks K_{{3,2}}^{{(2)}} integers {{2,3,5,8,9,10,12,25,30,45,60}}\n");

    println!("--- 213 couplings ---");
    show("1/α_GUT (lo)", &s.0 * nat(25), s.1.clone());
    show("1/α_GUT (hi)", &u.0 * nat(25), u.1.clone());
    show("1/α_em (CODATA)", nat(1370359991), nat(10_000_000));
    show("1/α_3 (v2)", nat(8475971), nat(1_000_000));
    show("1/α_2 (v2)", nat(29597268), nat(1_000_000));

    println!("\n--- ζ(2)-related ---");
    show("ζ(2) (lo, S(N))", s.0.clone(), s.1.clone());
    show("π² ≈ 6·ζ(2) (lo)", &s.0 * nat(6), s.1.clone());

    println!("\n--- Null hypothesis (no 213) ---");
    show("e", nat(271828182846), nat(100_000_000_000));
    show("π", nat(314159265359), nat(100_000_000_000));
    show("√2", nat(141421356237), nat(100_000_000_000));
    show("φ = (1+√5)/2", nat(161803398875), nat(100_000_000_000));
    show("ζ(3) Apéry", nat(120205690316), nat(100_000_000_000));

    println!("\nReading: ★ density in 213 vs null tests if pattern is real.");
}
