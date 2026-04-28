//! `alpha-em-decompose` — show structural origin of every integer
//! coefficient in 1/α_em(IR) and verify the sum at large N.
//!
//! Each term traces to a 213 lattice quantity (cited Lean theorem):
//!   E·d · ζ(2)         (edge count × atomic dim × Basel sum)
//!   1/α_2 = 30         (paper 2 gauge value)
//!   d²/NS = 25/3       (channels per spatial dim)
//!   α_GUT/(NS+1)       (Dyson tail at face dim)
//!   α_GUT/(NS²·d)      (proposed next correction; gap candidate)

use drlt_app::basel::{s_partial, upper};
use drlt_app::gap_explorer::{decimal, nat};
use num_bigint::BigUint;

const NS: u64 = 3;
const NT: u64 = 2;
const D:  u64 = 5;
const C_MULT: u64 = 2;

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(2000);

    let e = C_MULT * NS * NT;          // edge count = 12
    let s = s_partial(n);
    let u = upper(n);

    println!("=== 1/α_em(IR) structural decomposition (N = {n}) ===\n");
    println!("Lattice atoms: NS={NS}, NT={NT}, d=NS+NT={D}, c={C_MULT}");
    println!("Derived:       E = c·NS·NT = {e}, NS²·d = {}", NS*NS*D);
    println!();

    // Term 1 tight: 60·(S(N) + 1/(N+1)) = E·d·tight(ζ(2))
    //   = (60·s.0·(N+1) + 60·s.1) / (s.1·(N+1))
    let np1 = nat(n + 1);
    let coeff = nat(e * D);
    let t1 = (
        &coeff * &s.0 * &np1 + &coeff * &s.1,
        &s.1 * &np1,
    );
    println!("term 1 = E·d·ζ(2) (tight = 60·S(N) + 60/(N+1))");
    println!("       = {} · ζ(2)              ≈ {}", e * D, decimal(&t1, 9));

    // Term 2: 30 = 1/α_2
    let t2 = (nat(30), nat(1));
    println!("term 2 = 30  (= 1/α_2, paper 2)             ≈ {}", decimal(&t2, 9));

    // Term 3: d²/NS = 25/3
    let t3 = (nat(D * D), nat(NS));
    println!("term 3 = d²/NS = 25/3                       ≈ {}", decimal(&t3, 9));

    // α_GUT bracket lower: 1/(d²·upper)
    let agut: (BigUint, BigUint) = (u.1.clone(), nat(D * D) * &u.0);

    // Term 4: α_GUT/(NS+1) = α_GUT/4
    let t4 = (agut.0.clone(), &agut.1 * nat(NS + 1));
    println!("term 4 = α_GUT/(NS+1) = α_GUT/4 (Dyson)     ≈ {}", decimal(&t4, 9));

    // Term 5: α_GUT/(NS²·d) = α_GUT/45  ← proposed
    let t5 = (agut.0.clone(), &agut.1 * nat(NS * NS * D));
    println!("term 5 = α_GUT/(NS²·d) = α_GUT/45 [PROPOSED]≈ {}", decimal(&t5, 9));

    // Sum: term1 + term2 + term3 + term4 + term5
    fn add_q(a: &(BigUint, BigUint), b: &(BigUint, BigUint)) -> (BigUint, BigUint) {
        (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1)
    }
    let s12  = add_q(&t1, &t2);
    let s123 = add_q(&s12, &t3);
    let s1234 = add_q(&s123, &t4);
    let total = add_q(&s1234, &t5);

    println!();
    println!("Σ (terms 1–4, no proposed):    ≈ {}", decimal(&s1234, 9));
    println!("Σ (all 5, with proposed gap):  ≈ {}", decimal(&total, 9));
    println!("Observed 1/α_em (CODATA):       ≈ 137.035999100");
    println!();
    println!("Citations: AlphaEMStructure.{{sixty_is_E_times_d,");
    println!("           fortyfive_is_NS_sq_times_d, alpha_em_integer_origins}}");
}
