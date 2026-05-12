// Level 2 substitution search — find function f: base_invariant → asymptote
// fitting the 4 type's measured Moufang fail rate asymptotes.

#[derive(Clone, Debug)]
struct BaseInfo {
    name: &'static str,
    units: f64,
    cyclo_order: f64,
    nonab_frac: f64,
    gen_count: f64,
    center: f64,
    asymptote: f64,
    abelianization: f64,  // |G/[G,G]|
    commutator: f64,      // |[G,G]|
    conj_classes: f64,    // # of conjugacy classes
    order4_in_base: f64,  // # of order-4 elements in base unit group
}

fn types() -> Vec<BaseInfo> {
    vec![
        BaseInfo { name: "A",  units: 4.0,  cyclo_order: 4.0,  nonab_frac: 0.0,   gen_count: 1.0, center: 2.0, asymptote: 0.5000,
                   abelianization: 4.0, commutator: 1.0, conj_classes: 4.0, order4_in_base: 2.0 },
        BaseInfo { name: "B",  units: 2.0,  cyclo_order: 2.0,  nonab_frac: 0.0,   gen_count: 1.0, center: 2.0, asymptote: 0.5000,
                   abelianization: 2.0, commutator: 1.0, conj_classes: 2.0, order4_in_base: 0.0 },
        BaseInfo { name: "C",  units: 6.0,  cyclo_order: 6.0,  nonab_frac: 0.0,   gen_count: 1.0, center: 2.0, asymptote: 0.6892,
                   abelianization: 6.0, commutator: 1.0, conj_classes: 6.0, order4_in_base: 0.0 },
        BaseInfo { name: "D",  units: 24.0, cyclo_order: 12.0, nonab_frac: 0.292, gen_count: 4.0, center: 2.0, asymptote: 0.8093,
                   abelianization: 3.0, commutator: 8.0, conj_classes: 7.0, order4_in_base: 6.0 },
    ]
}

fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }

fn euler_phi(n: f64) -> f64 {
    let n = n as i64;
    (1..=n).filter(|k| gcd(*k, n) == 1).count() as f64
}

type Cand = (&'static str, fn(&BaseInfo) -> f64);

fn candidates() -> Vec<Cand> {
    let phi: f64 = (1.0 + 5.0_f64.sqrt()) / 2.0;  // golden ratio
    vec![
        ("1 - phi(u)/u",                       |b| 1.0 - euler_phi(b.units) / b.units),
        ("1 - phi(abel)/u",                    |b| 1.0 - euler_phi(b.abelianization) / b.units),
        ("1 - phi(abel)/abel",                 |b| 1.0 - euler_phi(b.abelianization) / b.abelianization),
        // ★ Golden ratio rank hypothesis
        ("1 - 0.5 · (1/φ_gold)^0  [rank=0]",   |_| 1.0 - 0.5 * 1.0),
        // The rank is hard to encode as a pure function — use a per-type lookup
        ("rank-based 1/φ_gold",                |b| {
            let phi: f64 = (1.0 + 5.0_f64.sqrt()) / 2.0;
            let rank: f64 = match b.name {
                "A" => 0.0,  // Z_4: 1 prime, abelian
                "B" => 0.0,  // Z_2: 1 prime, abelian
                "C" => 1.0,  // Z_6: 2 primes, abelian
                "D" => 2.0,  // 2T:  non-abelian
                _   => 0.0,
            };
            1.0 - 0.5 / phi.powf(rank)
        }),
        // Also try rational approximations
        ("rank-based 8/13",                    |b| {
            let r: f64 = 8.0 / 13.0;  // ≈ 0.615
            let rank: f64 = match b.name {
                "C" => 1.0, "D" => 2.0, _ => 0.0,
            };
            1.0 - 0.5 * r.powf(rank)
        }),
        ("rank-based 5/8",                     |b| {
            let r: f64 = 5.0 / 8.0;  // 0.625
            let rank: f64 = match b.name {
                "C" => 1.0, "D" => 2.0, _ => 0.0,
            };
            1.0 - 0.5 * r.powf(rank)
        }),
        ("rank-based 11/18",                   |b| {
            let r: f64 = 11.0 / 18.0;  // ≈ 0.611
            let rank: f64 = match b.name {
                "C" => 1.0, "D" => 2.0, _ => 0.0,
            };
            1.0 - 0.5 * r.powf(rank)
        }),
        ("(2·conj_classes - 6) / (2·conj_classes - 2)", |b| (2.0 * b.conj_classes - 6.0) / (2.0 * b.conj_classes - 2.0)),
        ("1 - 1/(0.5·conj + 1)",               |b| 1.0 - 1.0 / (0.5 * b.conj_classes + 1.0)),
    ]
}

fn fit(f: fn(&BaseInfo) -> f64, ts: &[BaseInfo]) -> (f64, Vec<f64>) {
    let preds: Vec<f64> = ts.iter().map(f).collect();
    let max_err = ts.iter().zip(&preds).map(|(t, p)| (t.asymptote - p).abs())
        .fold(0.0, f64::max);
    (max_err, preds)
}

fn main() {
    let ts = types();
    println!("# Level 2 substitution search: f(base) = asymptote\n");
    println!("Data:");
    for t in &ts { println!("  {} units={} cyclo={} nonab={} gen={} → asymp={}",
        t.name, t.units, t.cyclo_order, t.nonab_frac, t.gen_count, t.asymptote); }
    println!("\n--- Candidates ranked by max error ---\n");

    let mut results: Vec<(String, f64, Vec<f64>)> = candidates().into_iter()
        .map(|(name, f)| { let (e, p) = fit(f, &ts); (name.to_string(), e, p) })
        .collect();
    results.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
    for (name, err, preds) in results.iter().take(8) {
        println!("err={:.4}  {}", err, name);
        for (t, p) in ts.iter().zip(preds) {
            println!("   {} → pred {:.4} (obs {:.4}, dev {:+.4})",
                t.name, p, t.asymptote, t.asymptote - p);
        }
        println!();
    }
}
