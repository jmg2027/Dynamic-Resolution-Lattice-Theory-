// 213 algebra tower probe — ZSqrt[-2] Ln, n = 3..=6.
// Layer L_n = 2^(n-1) i64 components (pairs of Z_2 = ZSqrt[-2] base).

type V = Vec<i64>;

fn z2_mul(a: &[i64], b: &[i64]) -> V {
    vec![a[0] * b[0] - 2 * a[1] * b[1], a[0] * b[1] + a[1] * b[0]]
}
fn z2_conj(a: &[i64]) -> V { vec![a[0], -a[1]] }
fn z2_normsq(a: &[i64]) -> i64 { a[0] * a[0] + 2 * a[1] * a[1] }

fn add(a: &[i64], b: &[i64]) -> V { a.iter().zip(b).map(|(x, y)| x + y).collect() }
fn sub(a: &[i64], b: &[i64]) -> V { a.iter().zip(b).map(|(x, y)| x - y).collect() }
fn neg(a: &[i64]) -> V { a.iter().map(|x| -x).collect() }

fn cd_conj(a: &[i64]) -> V {
    let n = a.len();
    if n == 2 { return z2_conj(a); }
    let h = n / 2;
    let mut out = cd_conj(&a[..h]);
    out.extend(neg(&a[h..]));
    out
}

fn cd_normsq(a: &[i64]) -> i64 {
    let n = a.len();
    if n == 2 { return z2_normsq(a); }
    let h = n / 2;
    cd_normsq(&a[..h]) + cd_normsq(&a[h..])
}

fn cd_mul(a: &[i64], b: &[i64]) -> V {
    let n = a.len();
    if n == 2 { return z2_mul(a, b); }
    let h = n / 2;
    let (a_re, a_im) = (&a[..h], &a[h..]);
    let (b_re, b_im) = (&b[..h], &b[h..]);
    let new_re = sub(&cd_mul(a_re, b_re), &cd_mul(&cd_conj(b_im), a_im));
    let new_im = add(&cd_mul(b_im, a_re), &cd_mul(a_im, &cd_conj(b_re)));
    [new_re, new_im].concat()
}

fn zero(n: usize) -> V { vec![0; n] }
fn one(n: usize) -> V { let mut v = vec![0; n]; v[0] = 1; v }

fn enumerate_units(n: usize) -> Vec<V> {
    let dim = 1 << (n - 1);
    let mut units = Vec::new();
    for i in (0..dim).step_by(2) {
        for &s in &[1i64, -1] {
            let mut u = vec![0i64; dim];
            u[i] = s;
            units.push(u);
        }
    }
    units
}

fn order_of(u: &[i64], identity: &[i64]) -> usize {
    let mut cur = u.to_vec();
    for k in 1..=64 {
        if cur == identity { return k; }
        cur = cd_mul(&cur, u);
    }
    0
}

fn run_layer(n: usize) {
    let dim = 1 << (n - 1);
    let units = enumerate_units(n);
    let id = one(dim);
    println!("=== L{n} (dim={dim}, {} units) ===", units.len());

    let mut comm_bad = 0usize;
    for a in &units {
        for b in &units {
            if cd_mul(a, b) != cd_mul(b, a) { comm_bad += 1; }
        }
    }
    let total = units.len() * units.len();
    println!("comm:  {comm_bad}/{total}  ({:.1}% non-comm)",
        100.0 * comm_bad as f64 / total as f64);

    let mut assoc_bad = 0usize;
    for a in &units {
        for b in &units {
            let ab = cd_mul(a, b);
            for c in &units {
                if cd_mul(&ab, c) != cd_mul(a, &cd_mul(b, c)) { assoc_bad += 1; }
            }
        }
    }
    let assoc_total = units.len().pow(3);
    println!("assoc: {assoc_bad}/{assoc_total}  ({:.1}% non-assoc)",
        100.0 * assoc_bad as f64 / assoc_total as f64);

    let mut alt_l = 0usize; let mut alt_r = 0usize; let mut flex = 0usize;
    let mut moufang = 0usize;
    for a in &units {
        let aa = cd_mul(a, a);
        for b in &units {
            if cd_mul(a, &cd_mul(a, b)) != cd_mul(&aa, b) { alt_l += 1; }
            if cd_mul(&cd_mul(b, a), a) != cd_mul(b, &aa) { alt_r += 1; }
            if cd_mul(a, &cd_mul(b, a)) != cd_mul(&cd_mul(a, b), a) { flex += 1; }
        }
    }
    // Moufang: ((ab)a)c = a(b(ac))   — sample over a,b,c
    for a in &units { for b in &units { for c in &units {
        let lhs = cd_mul(&cd_mul(&cd_mul(a, b), a), c);
        let rhs = cd_mul(a, &cd_mul(b, &cd_mul(a, c)));
        if lhs != rhs { moufang += 1; }
    }}}
    println!("alt-L: {alt_l}/{total}   alt-R: {alt_r}/{total}   flex: {flex}/{total}");
    println!("Moufang ((ab)a)c=a(b(ac)): {moufang}/{assoc_total}");

    let mut nm_fail = 0usize;
    for a in &units {
        for b in &units {
            if cd_normsq(&cd_mul(a, b)) != cd_normsq(a) * cd_normsq(b) { nm_fail += 1; }
        }
    }
    println!("normMult fail (units): {nm_fail}/{total}");

    let mut counts = std::collections::BTreeMap::new();
    for u in &units { *counts.entry(order_of(u, &id)).or_insert(0usize) += 1; }
    print!("order dist:");
    for (k, c) in &counts { print!(" {{{k}:{c}}}"); }
    println!();

    let zero_v = zero(dim);
    let mut sums: Vec<V> = Vec::new();
    for (i, a) in units.iter().enumerate() {
        for b in units.iter().skip(i + 1) {
            let s = add(a, b);
            if s != zero_v { sums.push(s); }
        }
    }
    let mut zd = 0usize;
    let mut sample: Option<(V, V)> = None;
    for a in &sums {
        for b in &sums {
            if cd_mul(a, b) == zero_v {
                zd += 1;
                if sample.is_none() { sample = Some((a.clone(), b.clone())); }
            }
        }
    }
    println!("zero-divisor pairs (nonzero unit-sum * unit-sum): {zd}");
    if let Some((a, b)) = sample {
        println!("  sample a   = {a:?}");
        println!("  sample b   = {b:?}");
        println!("  normSq a={}, normSq b={}, normSq(a*b)={}",
            cd_normsq(&a), cd_normsq(&b), cd_normsq(&cd_mul(&a, &b)));
    }
    println!();
}

fn main() {
    for n in 3..=6 { run_layer(n); }
}
