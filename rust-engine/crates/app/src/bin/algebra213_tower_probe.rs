// 213 algebra tower probe — mul-table optimized.
use std::collections::HashMap;
type V = Vec<i64>;

#[derive(Clone, Copy)]
enum Base { ZSqrt(i64), ZOmega }
fn base_size(_: &Base) -> usize { 2 }

fn base_mul(b: &Base, a: &[i64], v: &[i64]) -> V {
    match b {
        Base::ZSqrt(d) => vec![a[0]*v[0] - d*a[1]*v[1], a[0]*v[1] + a[1]*v[0]],
        Base::ZOmega   => vec![a[0]*v[0] - a[1]*v[1], a[0]*v[1] + a[1]*v[0] - a[1]*v[1]],
    }
}
fn base_conj(b: &Base, a: &[i64]) -> V {
    match b {
        Base::ZSqrt(_) => vec![a[0], -a[1]],
        Base::ZOmega   => vec![a[0]-a[1], -a[1]],
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
    let id_idx = (0..nu).find(|&i| units[i][0] == 1 && units[i].iter().skip(1).all(|&x| x == 0)).unwrap();

    let mut comm = 0; let mut assoc = 0; let mut alt_l = 0; let mut alt_r = 0;
    let mut flex = 0; let mut mou = 0;
    for i in 0..nu {
        let ii = t[i][i];
        for j in 0..nu {
            if t[i][j] != t[j][i] { comm += 1; }
            if t[i][t[i][j]] != t[ii][j] { alt_l += 1; }
            if t[t[j][i]][i] != t[j][ii] { alt_r += 1; }
            if t[i][t[j][i]] != t[t[i][j]][i] { flex += 1; }
            let aj = t[i][j];
            for k in 0..nu {
                if t[aj][k] != t[i][t[j][k]] { assoc += 1; }
                let lhs = t[t[t[i][j]][i]][k];
                let rhs = t[i][t[j][t[i][k]]];
                if lhs != rhs { mou += 1; }
            }
        }
    }

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
    println!("# 213 algebra tower probe — Type C deep push\n");
    // Already-cached data for D=1, D=2 we know from previous runs.
    // This run focuses on ZOmega L8 (384 units, 56M triples) to determine
    // Type C Moufang-rate asymptote.
    run_layer(&Base::ZOmega, 8, "ZOmega");
}
