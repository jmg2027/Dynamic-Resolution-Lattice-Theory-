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
}

fn types() -> Vec<BaseInfo> {
    vec![
        BaseInfo { name: "A",  units: 4.0,  cyclo_order: 4.0,  nonab_frac: 0.0,   gen_count: 1.0, center: 2.0, asymptote: 0.5000 },
        BaseInfo { name: "B",  units: 2.0,  cyclo_order: 2.0,  nonab_frac: 0.0,   gen_count: 1.0, center: 2.0, asymptote: 0.5000 },
        BaseInfo { name: "C",  units: 6.0,  cyclo_order: 6.0,  nonab_frac: 0.0,   gen_count: 1.0, center: 2.0, asymptote: 0.6892 },
        BaseInfo { name: "D",  units: 24.0, cyclo_order: 12.0, nonab_frac: 0.292, gen_count: 4.0, center: 2.0, asymptote: 0.8093 },
    ]
}

fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }

fn euler_phi(n: f64) -> f64 {
    let n = n as i64;
    (1..=n).filter(|k| gcd(*k, n) == 1).count() as f64
}

type Cand = (&'static str, fn(&BaseInfo) -> f64);

fn candidates() -> Vec<Cand> {
    vec![
        ("(units - 2) / units",            |b| (b.units - 2.0) / b.units),
        ("1 - 2/units",                     |b| 1.0 - 2.0 / b.units),
        ("1 - 2/cyclo",                     |b| 1.0 - 2.0 / b.cyclo_order),
        ("(units - 2) / (units + 2)",       |b| (b.units - 2.0) / (b.units + 2.0)),
        ("1 - sqrt(2/units)",               |b| 1.0 - (2.0 / b.units).sqrt()),
        ("(units - 2) / (units + cyclo - 2)", |b| (b.units - 2.0) / (b.units + b.cyclo_order - 2.0)),
        ("(2u - 4) / (2u + cyclo)",         |b| (2.0 * b.units - 4.0) / (2.0 * b.units + b.cyclo_order)),
        ("1 - cyclo/(units · gen)",         |b| 1.0 - b.cyclo_order / (b.units * b.gen_count)),
        ("ln(u)/(ln(u)+ln(2))",             |b| b.units.ln() / (b.units.ln() + 2.0_f64.ln())),
        ("1 - phi(u)/u",                    |b| 1.0 - euler_phi(b.units) / b.units),
        ("(u^2 - 4) / (u^2 + 4)",           |b| (b.units.powi(2) - 4.0) / (b.units.powi(2) + 4.0)),
        ("1 - 2·gen/units",                 |b| 1.0 - 2.0 * b.gen_count / b.units),
        ("1/2 + nonab_frac",                |b| 0.5 + b.nonab_frac),
        ("0.5 · (1 + nonab_frac · 2)",      |b| 0.5 * (1.0 + b.nonab_frac * 2.0)),
        ("(units + 2·nonab·u) / (2u + 4)",  |b| (b.units + 2.0 * b.nonab_frac * b.units) / (2.0 * b.units + 4.0)),
        ("1 - 1/sqrt(u·gen)",               |b| 1.0 - 1.0 / (b.units * b.gen_count).sqrt()),
        ("(u + cyclo - 4) / (u + cyclo)",   |b| (b.units + b.cyclo_order - 4.0) / (b.units + b.cyclo_order)),
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
