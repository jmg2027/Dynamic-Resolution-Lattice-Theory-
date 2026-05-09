// 213 algebra tower probe — mul-table optimized.
use std::collections::HashMap;
type V = Vec<i64>;

#[derive(Clone, Copy)]
enum Base { ZSqrt(i64), ZOmega, Hurwitz }
fn base_size(b: &Base) -> usize {
    match b { Base::Hurwitz => 4, _ => 2 }
}

fn base_mul(b: &Base, a: &[i64], v: &[i64]) -> V {
    match b {
        Base::ZSqrt(d) => vec![a[0]*v[0] - d*a[1]*v[1], a[0]*v[1] + a[1]*v[0]],
        Base::ZOmega   => vec![a[0]*v[0] - a[1]*v[1], a[0]*v[1] + a[1]*v[0] - a[1]*v[1]],
        // Hurwitz: scaled rep (×2), quaternion mul, divide by 2 at end (closed for Hurwitz).
        Base::Hurwitz => vec![
            (a[0]*v[0] - a[1]*v[1] - a[2]*v[2] - a[3]*v[3]) / 2,
            (a[0]*v[1] + a[1]*v[0] + a[2]*v[3] - a[3]*v[2]) / 2,
            (a[0]*v[2] - a[1]*v[3] + a[2]*v[0] + a[3]*v[1]) / 2,
            (a[0]*v[3] + a[1]*v[2] - a[2]*v[1] + a[3]*v[0]) / 2,
        ],
    }
}
fn base_conj(b: &Base, a: &[i64]) -> V {
    match b {
        Base::ZSqrt(_) => vec![a[0], -a[1]],
        Base::ZOmega   => vec![a[0]-a[1], -a[1]],
        Base::Hurwitz  => vec![a[0], -a[1], -a[2], -a[3]],
    }
}
fn base_units(b: &Base) -> Vec<V> {
    match b {
        Base::ZSqrt(d) => {
            let mut us = vec![vec![1,0], vec![-1,0]];
            if *d == 1 { us.push(vec![0,1]); us.push(vec![0,-1]); }
            us
        }
        Base::ZOmega => vec![vec![1,0],vec![-1,0],vec![0,1],vec![0,-1],vec![1,1],vec![-1,-1]],
        Base::Hurwitz => {
            // scaled ×2: 8 Lipschitz axis ±2 in one slot + 16 half-integer ±1 in all slots.
            let mut us = Vec::new();
            for i in 0..4 {
                for &s in &[2i64, -2] {
                    let mut u = vec![0i64; 4]; u[i] = s; us.push(u);
                }
            }
            for &a in &[1i64, -1] { for &b in &[1i64, -1] {
                for &c in &[1i64, -1] { for &d in &[1i64, -1] {
                    us.push(vec![a, b, c, d]);
                }}
            }}
            us
        }
    }
}

fn add(a: &[i64], b: &[i64]) -> V { a.iter().zip(b).map(|(x,y)| x+y).collect() }
fn sub(a: &[i64], b: &[i64]) -> V { a.iter().zip(b).map(|(x,y)| x-y).collect() }
fn neg(a: &[i64]) -> V { a.iter().map(|x| -x).collect() }

fn cd_conj(b: &Base, a: &[i64]) -> V {
    if a.len() == base_size(b) { return base_conj(b, a); }
    let h = a.len()/2;
    let mut out = cd_conj(b, &a[..h]);
    out.extend(neg(&a[h..]));
    out
}
fn cd_mul(b: &Base, a: &[i64], v: &[i64]) -> V {
    if a.len() == base_size(b) { return base_mul(b, a, v); }
    let h = a.len()/2;
    let (ar, ai) = (&a[..h], &a[h..]);
    let (vr, vi) = (&v[..h], &v[h..]);
    let new_re = sub(&cd_mul(b, ar, vr), &cd_mul(b, &cd_conj(b, vi), ai));
    let new_im = add(&cd_mul(b, vi, ar), &cd_mul(b, ai, &cd_conj(b, vr)));
    [new_re, new_im].concat()
}

fn enumerate_units(b: &Base, n: usize) -> Vec<V> {
    let mut cur = base_units(b);
    for _ in 2..n {
        let h = cur[0].len();
        let mut nx = Vec::new();
        for u in &cur {
            let mut l = u.clone(); l.extend(vec![0; h]); nx.push(l);
            let mut r = vec![0; h]; r.extend(u.iter()); nx.push(r);
        }
        cur = nx;
    }
    cur
}

fn build_mul_table(b: &Base, units: &[V]) -> Vec<Vec<usize>> {
    let lookup: HashMap<V, usize> =
        units.iter().cloned().enumerate().map(|(i,u)| (u,i)).collect();
    let n = units.len();
    let mut t = vec![vec![0usize; n]; n];
    for i in 0..n {
        for j in 0..n {
            let p = cd_mul(b, &units[i], &units[j]);
            t[i][j] = *lookup.get(&p).expect("nm-fail: unit×unit not in unit set");
        }
    }
    t
}

fn run_layer(b: &Base, n: usize, name: &str) {
    let units = enumerate_units(b, n);
    let dim = units[0].len();
    let nu = units.len();
    let t = build_mul_table(b, &units);
    let id_first: i64 = match b { Base::Hurwitz => 2, _ => 1 };
    let id_idx = (0..nu).find(|&i| units[i][0] == id_first && units[i].iter().skip(1).all(|&x| x == 0)).unwrap();

    // Multi-threaded: chunks of `i` distributed across N threads.
    let n_threads = std::thread::available_parallelism().map(|p| p.get()).unwrap_or(4);
    let chunk_size = (nu + n_threads - 1) / n_threads;
    let totals: Vec<(usize, usize, usize, usize, usize, usize)> =
        std::thread::scope(|s| {
            let handles: Vec<_> = (0..n_threads).map(|c| {
                let start = c * chunk_size;
                let end = ((c + 1) * chunk_size).min(nu);
                let t_ref = &t;
                s.spawn(move || {
                    let mut lc = 0; let mut la = 0; let mut ll = 0; let mut lr = 0;
                    let mut lf = 0; let mut lm = 0;
                    for i in start..end {
                        let ii = t_ref[i][i];
                        for j in 0..nu {
                            if t_ref[i][j] != t_ref[j][i] { lc += 1; }
                            if t_ref[i][t_ref[i][j]] != t_ref[ii][j] { ll += 1; }
                            if t_ref[t_ref[j][i]][i] != t_ref[j][ii] { lr += 1; }
                            if t_ref[i][t_ref[j][i]] != t_ref[t_ref[i][j]][i] { lf += 1; }
                            let aj = t_ref[i][j];
                            for k in 0..nu {
                                if t_ref[aj][k] != t_ref[i][t_ref[j][k]] { la += 1; }
                                let lhs = t_ref[t_ref[t_ref[i][j]][i]][k];
                                let rhs = t_ref[i][t_ref[j][t_ref[i][k]]];
                                if lhs != rhs { lm += 1; }
                            }
                        }
                    }
                    (lc, la, ll, lr, lf, lm)
                })
            }).collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
    let (comm, assoc, alt_l, alt_r, flex, mou) = totals.iter().fold((0,0,0,0,0,0),
        |a, b| (a.0+b.0, a.1+b.1, a.2+b.2, a.3+b.3, a.4+b.4, a.5+b.5));

    let total = nu * nu;
    let assoc_total = nu.pow(3);

    // order distribution via table walk
    let mut counts = std::collections::BTreeMap::new();
    for i in 0..nu {
        let mut cur = i;
        let mut ord = 0;
        for k in 1..=128 {
            if cur == id_idx { ord = k; break; }
            cur = t[cur][i];
        }
        *counts.entry(ord).or_insert(0usize) += 1;
    }
    let order_str: String = counts.iter().map(|(k,c)| format!("{k}:{c}")).collect::<Vec<_>>().join(",");

    // power-associativity (still on units)
    let mut pa = 0;
    for i in 0..nu {
        let ii = t[i][i];
        if t[ii][i] != t[i][ii] { pa += 1; }
    }

    println!("{name} L{n} dim={dim} units={nu}");
    println!("  comm={comm}/{total}  assoc={assoc}/{assoc_total}");
    println!("  alt-L={alt_l} alt-R={alt_r} flex={flex} Mou={mou}/{assoc_total} pow-assoc-viol={pa}");
    println!("  order={{{order_str}}}");
    println!();
}

fn main() {
    println!("# 213 algebra tower probe — Type D Hurwitz raid\n");
    // Hurwitz base (24 units) — predicts L3 Moufang loss already.
    for n in 2..=7 {
        run_layer(&Base::Hurwitz, n, "Hurwitz");
    }
}
