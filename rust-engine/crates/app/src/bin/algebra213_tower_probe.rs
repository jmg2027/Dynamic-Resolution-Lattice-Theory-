// 213 algebra tower probe — generic base × layer cross-section.
// Bases: ZSqrt(D) for D ≥ 1, ZOmega = ℤ[ω] (ω³ = 1).
// L_n = "n-2 CD doublings of base"; component count = 2 × (base components) × 2^(n-2).

type V = Vec<i64>;

#[derive(Clone, Copy)]
enum Base {
    ZSqrt(i64),  // ℤ[√-D]: norm a²+Db², conj (a, -b), mul (a₀b₀-Da₁b₁, a₀b₁+a₁b₀)
    ZOmega,       // ℤ[ω]:    norm a²-ab+b², conj (a-b, -b), mul (a₀b₀-a₁b₁, a₀b₁+a₁b₀-a₁b₁)
}

fn base_size(_b: &Base) -> usize { 2 }

fn base_mul(b: &Base, a: &[i64], v: &[i64]) -> V {
    match b {
        Base::ZSqrt(d) => vec![a[0]*v[0] - d*a[1]*v[1], a[0]*v[1] + a[1]*v[0]],
        Base::ZOmega   => vec![a[0]*v[0] - a[1]*v[1], a[0]*v[1] + a[1]*v[0] - a[1]*v[1]],
    }
}
fn base_conj(b: &Base, a: &[i64]) -> V {
    match b {
        Base::ZSqrt(_) => vec![a[0], -a[1]],
        Base::ZOmega   => vec![a[0] - a[1], -a[1]],
    }
}
fn base_normsq(b: &Base, a: &[i64]) -> i64 {
    match b {
        Base::ZSqrt(d) => a[0]*a[0] + d * a[1]*a[1],
        Base::ZOmega   => a[0]*a[0] - a[0]*a[1] + a[1]*a[1],
    }
}
fn base_units(b: &Base) -> Vec<V> {
    match b {
        Base::ZSqrt(d) => {
            let mut us = vec![vec![1, 0], vec![-1, 0]];
            if *d == 1 { us.push(vec![0, 1]); us.push(vec![0, -1]); }
            us
        }
        Base::ZOmega => {
            // 6 units: ±1, ±ω, ±(1+ω) ... actually solving a²-ab+b² = 1
            //   (1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)
            vec![vec![1,0], vec![-1,0], vec![0,1], vec![0,-1], vec![1,1], vec![-1,-1]]
        }
    }
}

fn add(a: &[i64], b: &[i64]) -> V { a.iter().zip(b).map(|(x,y)| x+y).collect() }
fn sub(a: &[i64], b: &[i64]) -> V { a.iter().zip(b).map(|(x,y)| x-y).collect() }
fn neg(a: &[i64]) -> V { a.iter().map(|x| -x).collect() }

fn cd_conj(b: &Base, a: &[i64]) -> V {
    if a.len() == base_size(b) { return base_conj(b, a); }
    let h = a.len() / 2;
    let mut out = cd_conj(b, &a[..h]);
    out.extend(neg(&a[h..]));
    out
}
fn cd_normsq(b: &Base, a: &[i64]) -> i64 {
    if a.len() == base_size(b) { return base_normsq(b, a); }
    let h = a.len() / 2;
    cd_normsq(b, &a[..h]) + cd_normsq(b, &a[h..])
}
fn cd_mul(b: &Base, a: &[i64], v: &[i64]) -> V {
    if a.len() == base_size(b) { return base_mul(b, a, v); }
    let h = a.len() / 2;
    let (ar, ai) = (&a[..h], &a[h..]);
    let (vr, vi) = (&v[..h], &v[h..]);
    let new_re = sub(&cd_mul(b, ar, vr), &cd_mul(b, &cd_conj(b, vi), ai));
    let new_im = add(&cd_mul(b, vi, ar), &cd_mul(b, ai, &cd_conj(b, vr)));
    [new_re, new_im].concat()
}

fn zero(n: usize) -> V { vec![0; n] }
fn one(n: usize) -> V { let mut v = vec![0; n]; v[0] = 1; v }

// Recursively enumerate L_n units: L_n units = {(u, 0)} ∪ {(0, u)} for u ∈ L_{n-1} units.
fn enumerate_units(b: &Base, n: usize) -> Vec<V> {
    let mut current: Vec<V> = base_units(b);
    for _ in 2..n {
        let half_dim = current[0].len();
        let mut next = Vec::new();
        for u in &current {
            let mut left = u.clone(); left.extend(vec![0; half_dim]);
            next.push(left);
            let mut right = vec![0; half_dim]; right.extend(u.iter());
            next.push(right);
        }
        current = next;
    }
    current
}

fn order_of(b: &Base, u: &[i64], identity: &[i64]) -> usize {
    let mut cur = u.to_vec();
    for k in 1..=128 {
        if cur == identity { return k; }
        cur = cd_mul(b, &cur, u);
    }
    0
}

fn run_layer(b: &Base, n: usize, name: &str) {
    let units = enumerate_units(b, n);
    let dim = units[0].len();
    let id = one(dim);
    let nu = units.len();
    let total = nu * nu;
    let assoc_total = nu.pow(3);

    let (mut comm, mut assoc, mut alt_l, mut alt_r, mut flex, mut mou, mut nm) =
        (0,0,0,0,0,0,0);
    for a in &units {
        let aa = cd_mul(b, a, a);
        for v in &units {
            if cd_mul(b, a, v) != cd_mul(b, v, a) { comm += 1; }
            if cd_mul(b, a, &cd_mul(b, a, v)) != cd_mul(b, &aa, v) { alt_l += 1; }
            if cd_mul(b, &cd_mul(b, v, a), a) != cd_mul(b, v, &aa) { alt_r += 1; }
            if cd_mul(b, a, &cd_mul(b, v, a)) != cd_mul(b, &cd_mul(b, a, v), a) { flex += 1; }
            if cd_normsq(b, &cd_mul(b, a, v)) != cd_normsq(b, a) * cd_normsq(b, v) { nm += 1; }
            let av = cd_mul(b, a, v);
            for c in &units {
                if cd_mul(b, &av, c) != cd_mul(b, a, &cd_mul(b, v, c)) { assoc += 1; }
                let lhs = cd_mul(b, &cd_mul(b, &cd_mul(b, a, v), a), c);
                let rhs = cd_mul(b, a, &cd_mul(b, v, &cd_mul(b, a, c)));
                if lhs != rhs { mou += 1; }
            }
        }
    }
    let mut counts = std::collections::BTreeMap::new();
    for u in &units { *counts.entry(order_of(b, u, &id)).or_insert(0usize) += 1; }
    let order_str: String = counts.iter().map(|(k,c)| format!("{k}:{c}")).collect::<Vec<_>>().join(",");

    println!("{name} L{n}  dim={dim} units={nu}");
    println!("  comm={comm}/{total}  assoc={assoc}/{assoc_total}");
    println!("  alt-L={alt_l}  alt-R={alt_r}  flex={flex}  Moufang={mou}/{assoc_total}  nm-fail={nm}");
    println!("  order_dist={{{order_str}}}");
    println!();
}

fn main() {
    println!("# 213 algebra tower — generic base × layer probe\n");
    for n in 3..=6 {
        run_layer(&Base::ZSqrt(1),  n, "D=1     ");
        run_layer(&Base::ZSqrt(2),  n, "D=2     ");
        run_layer(&Base::ZOmega,    n, "ZOmega  ");
        println!("─────────────────────────────────────────");
    }
}
