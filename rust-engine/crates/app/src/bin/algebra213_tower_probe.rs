// 213 algebra tower probe — generic ZSqrt(D) base, D ∈ {1, 2, ...}, layer ∈ {3..6}.
// L_n = 2^(n-1) i64 components; D=1 → ZI (Gaussian) base, D=2 → ZSqrt[-2] base, etc.

type V = Vec<i64>;

fn zd_mul(d: i64, a: &[i64], b: &[i64]) -> V {
    vec![a[0] * b[0] - d * a[1] * b[1], a[0] * b[1] + a[1] * b[0]]
}
fn zd_conj(a: &[i64]) -> V { vec![a[0], -a[1]] }
fn zd_normsq(d: i64, a: &[i64]) -> i64 { a[0] * a[0] + d * a[1] * a[1] }

fn add(a: &[i64], b: &[i64]) -> V { a.iter().zip(b).map(|(x, y)| x + y).collect() }
fn sub(a: &[i64], b: &[i64]) -> V { a.iter().zip(b).map(|(x, y)| x - y).collect() }
fn neg(a: &[i64]) -> V { a.iter().map(|x| -x).collect() }

fn cd_conj(a: &[i64]) -> V {
    let n = a.len();
    if n == 2 { return zd_conj(a); }
    let h = n / 2;
    let mut out = cd_conj(&a[..h]);
    out.extend(neg(&a[h..]));
    out
}
fn cd_normsq(d: i64, a: &[i64]) -> i64 {
    let n = a.len();
    if n == 2 { return zd_normsq(d, a); }
    let h = n / 2;
    cd_normsq(d, &a[..h]) + cd_normsq(d, &a[h..])
}
fn cd_mul(d: i64, a: &[i64], b: &[i64]) -> V {
    let n = a.len();
    if n == 2 { return zd_mul(d, a, b); }
    let h = n / 2;
    let (a_re, a_im) = (&a[..h], &a[h..]);
    let (b_re, b_im) = (&b[..h], &b[h..]);
    let new_re = sub(&cd_mul(d, a_re, b_re), &cd_mul(d, &cd_conj(b_im), a_im));
    let new_im = add(&cd_mul(d, b_im, a_re), &cd_mul(d, a_im, &cd_conj(b_re)));
    [new_re, new_im].concat()
}

fn zero(n: usize) -> V { vec![0; n] }
fn one(n: usize) -> V { let mut v = vec![0; n]; v[0] = 1; v }

// Units: ±1 at any position contributing weight 1 to the norm.
// For D=1, every position has weight 1. For D≠1, only "real-slot" positions
// (even indices at deepest level) have weight 1; "im" positions have weight D.
fn enumerate_units(d: i64, n: usize) -> Vec<V> {
    let dim = 1 << (n - 1);
    let step = if d == 1 { 1 } else { 2 };
    let mut units = Vec::new();
    for i in (0..dim).step_by(step) {
        for &s in &[1i64, -1] {
            let mut u = vec![0i64; dim];
            u[i] = s;
            units.push(u);
        }
    }
    units
}

fn order_of(d: i64, u: &[i64], identity: &[i64]) -> usize {
    let mut cur = u.to_vec();
    for k in 1..=128 {
        if cur == identity { return k; }
        cur = cd_mul(d, &cur, u);
    }
    0
}

fn run_layer(d: i64, n: usize) {
    let dim = 1 << (n - 1);
    let units = enumerate_units(d, n);
    let id = one(dim);
    let nu = units.len();
    let total = nu * nu;
    let assoc_total = nu.pow(3);

    let mut comm_bad = 0;
    let mut assoc_bad = 0;
    let mut alt_l = 0; let mut alt_r = 0; let mut flex = 0; let mut moufang = 0;
    let mut nm_fail = 0;
    for a in &units {
        let aa = cd_mul(d, a, a);
        for b in &units {
            if cd_mul(d, a, b) != cd_mul(d, b, a) { comm_bad += 1; }
            if cd_mul(d, a, &cd_mul(d, a, b)) != cd_mul(d, &aa, b) { alt_l += 1; }
            if cd_mul(d, &cd_mul(d, b, a), a) != cd_mul(d, b, &aa) { alt_r += 1; }
            if cd_mul(d, a, &cd_mul(d, b, a)) != cd_mul(d, &cd_mul(d, a, b), a) { flex += 1; }
            if cd_normsq(d, &cd_mul(d, a, b)) != cd_normsq(d, a) * cd_normsq(d, b) { nm_fail += 1; }
            let ab = cd_mul(d, a, b);
            for c in &units {
                if cd_mul(d, &ab, c) != cd_mul(d, a, &cd_mul(d, b, c)) { assoc_bad += 1; }
                let lhs = cd_mul(d, &cd_mul(d, &cd_mul(d, a, b), a), c);
                let rhs = cd_mul(d, a, &cd_mul(d, b, &cd_mul(d, a, c)));
                if lhs != rhs { moufang += 1; }
            }
        }
    }

    let mut counts = std::collections::BTreeMap::new();
    for u in &units { *counts.entry(order_of(d, u, &id)).or_insert(0usize) += 1; }
    let order_str: String = counts.iter().map(|(k,c)| format!("{k}:{c}")).collect::<Vec<_>>().join(",");

    // Zero divisor search via nonzero unit-sum products
    let zero_v = zero(dim);
    let mut sums: Vec<V> = Vec::new();
    for (i, a) in units.iter().enumerate() {
        for b in units.iter().skip(i + 1) {
            let s = add(a, b);
            if s != zero_v { sums.push(s); }
        }
    }
    let mut zd = 0;
    let mut zd_sample: Option<(V, V)> = None;
    'outer: for a in &sums {
        for b in &sums {
            if cd_mul(d, a, b) == zero_v {
                zd += 1;
                if zd_sample.is_none() { zd_sample = Some((a.clone(), b.clone())); }
                if zd > 100 { break 'outer; }  // cap, just need existence
            }
        }
    }

    println!("D={d} L{n} dim={dim} units={nu}");
    println!("  comm_fail={comm_bad}/{total}  assoc_fail={assoc_bad}/{assoc_total}");
    println!("  alt-L={alt_l}/{total}  alt-R={alt_r}/{total}  flex={flex}/{total}");
    println!("  Moufang={moufang}/{assoc_total}  normMult_fail={nm_fail}/{total}");
    println!("  order_dist={{{order_str}}}");
    println!("  zd_count={zd}");
    if let Some((a, b)) = &zd_sample {
        println!("  zd_a={:?}", a);
        println!("  zd_b={:?}", b);
    }
    println!();
}

fn main() {
    println!("# 213 algebra tower probe — base D × layer L_n cross-section");
    println!("# (alt-L/R/flex/Moufang/normMult/zd measured on units)\n");
    for &d in &[1i64, 2, 3, 5, 7] {
        for n in 3..=5 {  // L=6 too slow if we test many D
            run_layer(d, n);
        }
    }
}
