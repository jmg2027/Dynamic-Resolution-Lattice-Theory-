//! `impedance-search` — bottom-up: try natural impedance functions
//! C(i, j) on the 31 sub-simplices, sum Σ chiralDim(i,j)·C(i,j),
//! compare to 137.036.  Known terms appear at the end as cross-check.

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, lt_q, nat};
use drlt_hypervisor::chiral_k32::chiral_dim;

const NS: u64 = 3;
const NT: u64 = 2;

fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn mul_n(a: &Q, n: u64) -> Q { (&a.0 * nat(n), a.1.clone()) }
fn zero() -> Q { (nat(0), nat(1)) }

fn evaluate<F: Fn(u64, u64) -> Q>(c: F) -> Q {
    let mut t = zero();
    for i in 0..=NS { for j in 0..=NT {
        if i + j == 0 { continue; }
        let cd = chiral_dim(i, j); if cd == 0 { continue; }
        t = add_q(&t, &mul_n(&c(i, j), cd));
    }}
    t
}

fn main() {
    let n = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(2000u64);
    let s = s_partial(n);
    let obs = (nat(1370359991u64), nat(10_000_000));
    println!("=== Impedance search on 31 sub-simplices (N = {n}) ===");
    println!("Target observed 1/α_em ≈ {}\n", decimal(&obs, 9));

    let trials: Vec<(&str, Box<dyn Fn(u64, u64) -> Q>)> = vec![
        ("C = 1",                          Box::new(|_, _| (nat(1), nat(1)))),
        ("C = i + j",                      Box::new(|i, j| (nat(i + j), nat(1)))),
        ("C = (i+j)(i+j-1)/2 (#pairs)",    Box::new(|i, j|
            (nat((i+j)*(i+j).saturating_sub(1)/2), nat(1)))),
        ("C = i² + j²",                    Box::new(|i, j| (nat(i*i + j*j), nat(1)))),
        ("C = i · j",                      Box::new(|i, j| (nat(i*j), nat(1)))),
        ("C = (i+j)·ζ(2)",                 Box::new({ let s = s.clone();
            move |i, j| (&s.0 * nat(i + j), s.1.clone()) })),
        ("C = ζ(2)  (constant)",           Box::new({ let s = s.clone();
            move |_, _| s.clone() })),
        ("C = 10·ζ(2) on (1,1) only",      Box::new({ let s = s.clone();
            move |i, j| if i==1 && j==1 { mul_n(&s, 10) } else { zero() } })),
        ("C = i²+j² · ζ(2)",               Box::new({ let s = s.clone();
            move |i, j| (&s.0 * nat(i*i + j*j), s.1.clone()) })),
    ];

    println!("{:<30}  {:<14}  {:>10}", "ansatz", "value", "Δ/obs");
    println!("{}", "─".repeat(60));
    for (name, f) in &trials {
        let t = evaluate(|i, j| f(i, j));
        let diff = if lt_q(&t, &obs)
            { (&obs.0 * &t.1 - &t.0 * &obs.1, &obs.1 * &t.1) }
            else { (&t.0 * &obs.1 - &obs.0 * &t.1, &obs.1 * &t.1) };
        let dr: Q = (&diff.0 * nat(1_000_000) * &obs.1, &diff.1 * &obs.0);
        println!("{:<30}  {:<14}  {:>10}", name, decimal(&t, 6), decimal(&dr, 0));
    }

    println!("\n=== Cross-check: known 5-term decomposition ===");
    println!("60·ζ(2) + 30 + 25/3 + α_GUT/4 + α_GUT/45 ≈ 137.0359951");
    println!("Cite: AlphaEMStructure.alpha_em_integer_origins (0-axiom)");
}
