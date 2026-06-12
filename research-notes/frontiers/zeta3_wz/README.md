# ζ(3) nucleus — Apéry's recurrence for `Bₙ` (the WZ identity)

The single remaining nucleus of the ζ(3) `zeta3HolonomicReal` program (see
`../zeta3_blueprint.md` "THE NUCLEUS").  Everything else — Brick 1 (lcm race),
Brick 2 (KeyDiv + Heart + engines), the `c n` integrality input — is PURE-landed.

## The target (Lean anchor: `lean/E213/Lib/Math/NumberTheory/AperyRecurrence.lean`)

`B(n) = Σ_{k=0}^n C(n,k)²·C(n+k,k)²`  (binomial Apéry numbers, manifestly `ℕ`).

> **`(j+2)³·B(j+2) + (j+1)³·B(j) = aperyLead(j)·B(j+1)`**,  `aperyLead j = 34j³+153j²+231j+117`.

Once proven `∀ j`, `zeta3Den n = (n!)³·B(n)` follows by induction (seeds
`B0=1, B1=5` match), closing the recurrence-divisibility route.

## Verified facts (run `python3 verify_recurrence.py`)

  * `B = [1, 5, 73, 1445, 33001, 819005, …]`; the recurrence holds (checked `j≤5`).
  * **The WZ combination sums to zero**: with
    `F(j,k) := (j+2)³b(j+2,k) + (j+1)³b(j,k) − aperyLead(j)b(j+1,k)`,
    `b(n,k)=C(n,k)²C(n+k,k)²`, one has `Σ_k F(j,k) = 0` (checked `j≤6`).  So `F`
    telescopes: `F(j,k) = G(j,k) − G(j,k−1)` for a certificate `G`.
  * `F(j,k) = R_F(j,k)·b(j,k)` with the **exact** rational reduction
    ```
    R_F = -4(2j+3)·P₆(j,k) / [ (j-k+1)²(j-k+2)² ]
    P₆  = 4j⁶+36j⁵−10j⁴k²+7j⁴k+133j⁴−60j³k²+42j³k+258j³
          +4j²k⁴−10j²k³−130j²k²+93j²k+277j²+12jk⁴−30jk³−120jk²+90jk+156j
          +9k⁴−23k³−39k²+32k+36
    ```
    (the term ratios are `b(j+1,k)/b(j,k) = (j+k+1)²/(j+1-k)²`,
    `b(j+2,k)/b(j,k) = ((j+k+1)(j+k+2))²/((j+1-k)(j+2-k))²`,
    `b(j,k-1)/b(j,k) = k⁴/((j-k+1)²(j+k)²)`).

## ★★★ THE CERTIFICATE — FOUND + VERIFIED (`verify_certificate.py`)

Closed form (exact bivariate fit, 0 error; cleared telescoping verified on 400
random `(j,k)`):

```
cert(j,k) = -4k⁴(2j+3)(4j²+12j-2k²+3k+8) / ((j-k+1)²(j-k+2)²)        # G = cert·a(j,k)
```

The denominators clear via the binomial shift identity
`C(j,k)²/((j-k+1)²(j-k+2)²) = C(j+2,k)²/((j+1)²(j+2)²)`
(from `C(j,k)/(j+1-k) = C(j+1,k)/(j+1)`, twice).  Define the **cleared certificate**

```
Ĝ(j,k) := (j+1)²(j+2)²·G(j,k)
        = -4·k⁴·(2j+3)·(4j²+12j-2k²+3k+8)·C(j+2,k)²·C(j+k,k)²
```

Then the **verified all-polynomial telescoping identity** (no division) is

> **`(j+1)²(j+2)²·F(j,k) = Ĝ(j,k+1) − Ĝ(j,k)`**,  forward difference,

with `F(j,k) = (j+2)³a(j+2,k) + (j+1)³a(j,k) − aperyLead(j)·a(j+1,k)`,
`a(n,k)=C(n,k)²C(n+k,k)²`.  Boundary (verified): `Ĝ(j,0)=0` (`k⁴` factor),
`Ĝ(j,k)=0` for `k>j+2` (`C(j+2,k)=0`).  Summing `k=0…` telescopes to
`(j+1)²(j+2)²·Σ_k F = Ĝ(top) − Ĝ(0) = 0`, hence `Σ_k F = 0` = the recurrence.

## Then the Lean formalization (the marathon, now mechanical)

The nucleus is now a **mechanical** (large) ∅-axiom task — no open mathematics:
  1. **Per-`k` cleared identity** `(j+1)²(j+2)²·F(j,k) = Ĝ(j,k+1) − Ĝ(j,k)` as a
     Nat identity.  Sign care: `F` has a `−aperyLead` term and `Ĝ`'s factor
     `(4j²+12j−2k²+3k+8)` changes sign, so split into pos/neg parts and prove the
     all-additive form (move negatives across).  Clear every binomial to factorials
     (à la `AperyIntegrality.aperyTrinomial`/`choose_mul_factorials`) → `ring_nat`.
     ~6 distinct binomials (squared) × degree-≤7 coeffs ⇒ the bulk (~several hundred
     lines).
  2. **Telescoping sum** over `k` with `sumTo` (`sumTo_succ`, the difference
     telescopes); boundary terms vanish (`Ĝ(j,0)=0`, top via `choose_eq_zero_of_lt`).
  3. ⇒ `(j+2)³B(j+2) + (j+1)³B(j) = aperyLead(j)·B(j+1)` (cancel `(j+1)²(j+2)²>0`).
  4. **Induction** `zeta3Den n = (n!)³·B(n)` (seeds match; recurrence matches the
     factorial-cleared orbit) — closes the recurrence-divisibility route.

Estimate: a dedicated multi-session formalization, but **no certificate hunting
and no open math remain** — every step above is verified numerically/symbolically.
