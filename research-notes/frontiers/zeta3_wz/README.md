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

## STATUS (2026-06-12): DENOMINATOR DONE — numerator is the remaining half

  * **`apery_recurrence` PURE** (`AperyRecurrence.lean`, 45 PURE): the denominator
    recurrence `(j+2)³B(j+2)+(j+1)³B(j)=aperyLead(j)B(j+1)`, via the certificate below.
  * **`zeta3Den_eq` PURE** (`Zeta3Apery.lean`): `zeta3Den n = (n!)³·B(n)`.
  * **Remaining: numerator integrality** `(n!)³ ∣ 2lcm³·zeta3Num n`.  Verified
    (`verify_numerator.py`): `zeta3Num n = (n!)³·aₙ` (orbit `0,6,702,375186,…`),
    `aₙ = Σ_k C(n,k)²C(n+k,k)²·c_{n,k}` with `c_{n,k}=Σ_{j≤n}1/j³ +
    Σ_{m≤k}(−1)^{m−1}/(2m³C(n,m)C(n+m,m))` (rational, harmonic denominators);
    `aₙ` satisfies the **same** Apéry recurrence; `2lcm³aₙ ∈ ℤ`.  Needs:
    (i) the **numerator WZ** (the *harmonic* summand satisfies the recurrence —
    harder than the `B` certificate below: `c_{n,k}` adds partial-fraction terms),
    giving `zeta3Num=(n!)³·aₙ`; (ii) the **ℚ-free §4 assembly** `2lcm³aₙ∈ℕ` via
    `heart_lcm` (kernel) + `cube_dvd_lcm_cube` (harmonic) + pos/neg Nat split.
    Recurrence-divisibility does **not** shortcut it (the `(m+2)³` in `((m+2)!)³`
    won't match — same wall the `B`-sum route resolved).  This is a fresh marathon
    comparable to the denominator nucleus.  Then piecewise `(c,p,q)` ⟹
    `zeta3_reduced_conditional` ⟹ `zeta3HolonomicReal`.

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

## ★ KEY SIMPLIFICATION — the proof stays in pure ℕ (no `Int`, no sign split)

The certificate factor `Q(j,k) = 4j²+12j−2k²+3k+8` is **`> 0` for all `0 ≤ k ≤
j+2`** (verified `j<200`; min at `k=j+2` is `(2j+3)(j+2)`), i.e. throughout the
summation range; outside it `C(j+2,k)=0` kills the term.  So `Ĝ` is sign-definite
(`≤ 0`) in range, and the whole identity is an **all-additive ℕ identity** with the
*magnitude*

```
Gmag(j,k) := 4·k⁴·(2j+3)·((4j²+12j+3k+8) − 2k²)·C(j+2,k)²·C(j+k,k)²      -- ℕ subtraction OK
```

**The per-`k` identity — VERIFIED as an exact `ℕ` identity for ALL `k`** (Nat-
truncated `Q`; `a n k = C(n,k)²C(n+k,k)²`):

> `(j+1)²(j+2)²·[(j+2)³·a(j+2,k) + (j+1)³·a(j,k)]  +  Gmag(j,k+1)`
> `   =  (j+1)²(j+2)²·aperyLead(j)·a(j+1,k)  +  Gmag(j,k)`

No `Int`, no `fdPos/fdNeg` split — structurally **identical to
`AperyIntegrality.aperyTrinomial`, just larger**.  (Nat truncation of `Q` is safe:
where `Q` would go `<0`, `C(j+2,k)=0`.)

## Lean formalization — STATUS

The two hardest pieces are **DONE + PURE** in `AperyRecurrence.lean`:

  * ★ **`reduced_wz_identity`** — the polynomial core (above), in the additive
    `j=k+d` form, closed by `ring_nat` (after expanding `^` to products, which
    `ring_nat` requires).  **This is the mathematical heart of Apéry's recurrence.**
  * ★ **`colrec`** — `(n+1−k)·C(n+1,k) = (n+1)·C(n,k)`, the binomial `W`-factoring
    building block (via `choose_mul_factorials`).  Helpers `succ_sub_of_le`,
    `nat_sub_eq_zero` (pure).
  * **`sumTo_shift_eq`** — the telescoping lemma (pure-ℕ additive form).

  * ★ **Contiguity `W`-relations DONE + PURE** (`colA/colAB/colB/colC1/colC/G1a/G1b`
    and `R0/R1/R2/G1`, defs `Wfac/Qpoly/Gmag`).  `R0: a(j,k)·(j+1)²(j+2)² =
    W·(j+2−k)²(j+1−k)²`; `R1: …=W·(j+2−k)²(j+k+1)²`; `R2: …=W·(j+k+1)²(j+k+2)²`;
    `G1: Gmag(j,k+1)=4(2j+3)Q(j,k+1)(j+2−k)²(j+k+1)²·W`; `G0 = Gmag` def.

`AperyRecurrence.lean` now **31 PURE / 0 dirty**.  Remaining = the final assembly:

  1. **Per-`k` identity** `(j+1)²(j+2)²[(j+2)³a(j+2,k)+(j+1)³a(j,k)] + Gmag(j,k+1) =
     (j+1)²(j+2)²·aperyLead(j)·a(j+1,k) + Gmag(j,k)`.  Substitute `R2,R0,G1` (LHS) and
     `R1,G0` (RHS) ⇒ both sides `= Wfac · (reduced)`.  Then `reduced LHS = reduced
     RHS` is `reduced_wz_identity`.  **Bridge** (verified): for `k≤j`, set `d=j−k`;
     `reduced_wz_identity k (j−k)` matches term-for-term after `k+(j−k)=j`
     (`add_sub_of_le`), `(j−k)+2=j+2−k`, `(j−k)+1=j+1−k` (`succ_sub_of_le`), and
     `Qpoly j (k+1) = 4d²+8dk+12d+2k²+11k+9` (resolve the `−2(k+1)²` truncation,
     valid since `k+1≤j+2`).  **Boundary** `k∈{j+1,j+2}`: `reduced_wz_identity`
     (`d=j−k`) does not apply, but REDID still holds (verified `k≤j+2`); prove these
     two by substituting `k=j+1`/`k=j+2`, resolving `j+2−k`/`j+1−k` to `1`/`0`
     (`add_sub_cancel_left`), then `ring_nat`.  For `k>j+2`, `Wfac=0` (both sides `0`).
  2. **Sum** `k=0…j+2` (`sumTo (j+3)`): `Gmag` telescopes via `sumTo_shift_eq`
     (boundaries `Gmag(j,0)=0`, `Gmag(j,j+3)=0`); `a(j,k)=0` for `k>j` via
     `choose_eq_zero_of_lt` connects the partial sums to `B(j),B(j+1),B(j+2)`.
  3. ⇒ recurrence (cancel `(j+1)²(j+2)²>0` with `mul_left_cancel_pos`).
  4. **Induct** `zeta3Den n = (n!)³·B(n)` (seeds match; recurrence matches the
     `(n!)³`-cleared orbit `aperyOrbit`).

REDID-range fact (verified): the reduced identity holds for **all `k≤j+2`** (Nat-
trunc), fails only for `k>j+2` (where `Wfac=0`).  Verify: `python3
verify_certificate.py`.  **No open math remains** — the rest is Lean labor.
