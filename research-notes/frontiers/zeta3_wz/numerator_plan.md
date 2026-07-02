# ζ(3) numerator marathon — roadmap (opened 2026-06-12)

**Goal**: `(n!)³ ∣ 2·lcm(1..n)³·zeta3Num n` (the numerator side of
`zeta3_reduced_conditional`).  The denominator side is DONE (`zeta3Den_eq`,
`apery_recurrence`).  This is the symmetric — and **harder** — half.

## Verified structure (`verify_numerator.py`, `numwz.py`, `kwz.py`)

`zeta3Num n = (n!)³·aₙ` (orbit `0,6,702,375186,…`), with the numerator Apéry number
```
aₙ = A(n) = H₃(n)·B(n) + K(n)
H₃(n) = Σ_{j=1}^n 1/j³                                   (harmonic)
B(n)  = Σ_k C(n,k)²C(n+k,k)²                             (denominator Apéry, DONE)
K(n)  = Σ_k C(n,k)²C(n+k,k)²·κ(n,k),
κ(n,k)= Σ_{m=1}^k (−1)^{m−1}/(2m³·C(n,m)·C(n+m,m))       (kernel)
```

Two independent deliverables, both needed:

### (I) The numerator recurrence (⟹ `zeta3Num = (n!)³·A`)

`A` satisfies **Apéry's recurrence** `(j+2)³A(j+2)+(j+1)³A(j)=aperyLead(j)A(j+1)`
(verified).  Decomposes (verified) as:
  * **H₃ part** `(j+2)³H₃(j+2)B(j+2)+(j+1)³H₃(j)B(j)−aperyLead(j)H₃(j+1)B(j+1) =
    B(j+2)−B(j)` — follows from **`apery_recurrence`** (DONE) + `H₃(n)−H₃(n−1)=1/n³`
    telescoping.  Formalizable, but involves ℚ (clear by `lcm³`/`(n!)³`).
  * **K inhomogeneous recurrence** `(j+2)³K(j+2)+(j+1)³K(j)−aperyLead(j)K(j+1) =
    B(j)−B(j+2)` — the NEW hard piece.

Then `(n!)³A` satisfies the orbit recurrence (seeds `0,6`) ⟹ `zeta3Num=(n!)³A`
(2-step induction, exactly like `zeta3Den_eq`).

### (II) The integrality `2·lcm³·A(n) ∈ ℕ`

`2lcm³A = (2lcm³H₃(n))·B(n) + 2lcm³K(n)`:
  * **harmonic** `2lcm³H₃(n) = 2·Σ_j lcm³/j³ ∈ ℕ` (each `lcm³/j³∈ℕ` by
    `cube_dvd_lcm_cube`, DONE).  ⟹ first term `∈ℕ`.
  * **kernel** `2lcm³K(n) = Σ_k C(n,k)²C(n+k,k)²·Σ_m (−1)^{m−1}lcm³/(m³C(n,m)C(n+m,m))`;
    each `|term| = C(n,k)C(n+k,k)·(lcm³C(n,k)C(n+k,k)/(m³C(n,m)C(n+m,m))) ∈ ℕ` by
    **`heart_lcm`** (DONE).  Signs ⟹ pos/neg Nat split.  This is the Brick-2 §4
    ÷-free assembly (~400–600 lines).

## ★★ RE-READ (2026-07-02, extension-protocol V1 probe) — the wall is a CAP, and the language is named

The KEY FINDING below ("no clean WZ certificate") is re-read by the extension protocol
(`frontiers/exterior_as_extension.md` §5): it is a **cap for the `b`-only certificate
language** `{rational(j,k)·b(j,k)}`, not a wall for the problem.  Verified exactly
(`verify_c_increments.py`, Fractions, all `n < 20`):

> **The c-increment collapsing laws.**  With the half-weight carrier
> `w(n,k) = 1/(C(n,k)C(n+k,k))` (so `b·w = C(n,k)C(n+k,k) = √b`, an *integer*):
>   (1) `c(n,k) − c(n−1,k) = (−1)^k · w(n,k) / (n²(n−k))`   (cross-`n` — THE collapse)
>   (2) `c(n,k) − c(n,k−1) = (−1)^{k−1} · w(n,k) / (2k³)`   (cross-`k` — definitional)

Consequences:
  * **One law, both parts.**  `k=0` in (1) gives `1/n³` — the single increment law
    covers the harmonic (`H₃`) and kernel (`κ`) parts *together*.  The H₃/K split of
    this plan is a presentation choice, not a necessity: the A-recurrence can be
    attacked directly on `Σ_k b(n,k)·c(n,k)` via Abel summation + (1)+(2), everything
    rational over the carrier pair `(b, √b)`.
  * **The certificate lives one language up.**  `F_A`'s c-difference terms are
    `b·(rational·w) = rational·√b`; so the A/K certificate search belongs to
    `span{rational·b·c, rational·√b}` — where Δ-calculus is fully rational.  (Checked:
    the *naive* one-term correction `G_A = G_B·c(j,k) + √b·t` leaves `t` messy — the
    extended certificate needs the multi-shift ansatz or the hand derivation; the
    *language* is confirmed, the certificate is the next step.)
  * **Formalization — the algebraic core LANDED** (`NumberTheory/AperyCollapsing.lean`,
    6 PURE / 0 dirty): the half-weight carrier `sqw n k := C(n,k)·C(n+k,k)` with its two
    contiguities `sqw_shift_n` (`(n+1−m)·√b(n+1,m) = (n+1+m)·√b(n,m)`, two `colrec`s) and
    `sqw_shift_k` (`(k+1)²·√b(n,k+1) = (n−k)(n+k+1)·√b(n,k)`, `lowrec` + `choose_succ_mul`),
    plus the recombination `square_split` (`k² + (n+k)(n−k) = n²`), bundled as
    `collapsing_core`.  These three are exactly what the ℚ-proof of law (1) reduces to
    (the induction step is two lines given them).  **Remaining**: (iii) the cleared
    signed-sum assembly of the laws themselves (`HL`-style clearing of `c` +
    `cube_dvd_lcm_cube`/`heart_lcm` divisibilities + pos/neg split), then the Abel
    assembly of the A-recurrence over `(b, √b, c)`.

## ★★★ THE NUMERATOR CERTIFICATE — FOUND + VERIFIED (2026-07-02)

**The hand-derived kernel telescoping is unnecessary.**  In the extended language over
`(b, √b, c)` the numerator recurrence telescopes with an **explicit Gosper certificate**
(derivation + exact verification, all `j < 26`: `derive_numerator_certificate.py`):

1. Express `c` at the top row (collapsing law (1)):
   `F_A = F_B·c(j+2,k) − (j+1)³b(j,k)[Dₙ(j+1,k)+Dₙ(j+2,k)] + aL·b(j+1,k)Dₙ(j+2,k)`.
2. Abel on `Σ F_B·c(j+2,k)` with the known denominator certificate `Ĝ`.
3. The residual `U(j,k) = (−1)^k·√b(j,k)·u(j,k)` with `u` an explicit rational function
   (four contiguity-reduced pieces; see the script header).
4. **The certificate** (found by `gosper_sum`, verified exactly):
   ```
   ψ(j,k) = −(−1)^k · k(2j+3) · P₄(j,k) · √b(j,k) / ((j+1)(j+2)²(j−k+1)(j+k+1)(j+k+2))
   P₄ = 8j⁴+24j³k+48j³+31j²k²+107j²k+104j²+13jk³+86jk²+153jk+96j+18k³+60k²+70k+32
   ```
   with `U(j,k) = ψ(j,k+1) − ψ(j,k)` for `0 ≤ k ≤ j−1`, `ψ(j,0) = 0`.
5. **Boundary** (the `k=j` edge — the certificate's `(j−k+1)`-pole compensates the
   vanishing binomial, same phenomenon as the denominator's `k∈{j+1,j+2}` boundary):
   `ψ(j,j) + U(j,j) + U(j,j+1) + U(j,j+2) = 0`.

⟹ `Σ_k F_A = 0` — deliverable (I)'s recurrence — **by certificate verification**, the
same mechanical shape as the denominator (`reduced_wz_identity` route).

**The reduced identities (round-4 blueprint, each verified symbolically ≡ 0)** — dividing
by `(−1)^k√b(j,k)`, with `φ := −k(2j+3)P₄/((j+1)(j+2)²(j−k+1)(j+k+1)(j+k+2))` and
`ρ := √b(k+1)/√b(k) = (j−k)(j+k+1)/(k+1)²` (= `sqw_shift_k`):

  * **R-NUM** `u + ρ·φ(k+1) + φ = 0` (common denominator
    `(j+1)(j+2)²(k+1)(j−k+1)(j+k+1)(j+k+2)(j+k+3)`; cleared numerator ≡ 0) — the
    numerator analogue of `reduced_wz_identity`, THE per-`k` Lean target;
  * **R-BND** `φ(j,j) + u(j,j) − T1(j) = 0`, `T1 = 2(2j+1)(19j²+58j+45)/((j+1)(j+2)²)`
    (piecewise: aL-piece `2(2j+1)(17j²+51j+39)/((j+1)(j+2)²)`, Ĝ-piece
    `2(2j+1)(2j+3)/((j+1)(j+2))`) — the `k=j` edge;
  * **R-NIL** `U(j,j+2) ≡ 0` (`C(j+2,j+3)=0`).

Lean order: (a) cleared collapsing laws — **algebra core DONE** (`AperyCollapsing` §4,
18/0 PURE): `collapsing_step` = the `m = k+1` kernel-increment step of the ℚ-induction
proving law (1), cleared over the carrier triple `√b(n,k)√b(n,k+1)√b(n−1,k+1)`, additive
(`n = k+e+1`); proven by cancelling `(k+1)²(2k+e+2)` after converting to the
`√b(n,k)√b(n,k+1)`-basis (`sqw_shift_k_add`/`sqw_shift_n_add`), scalar residue =
`square_split` in disguise (keeping every `ring_nat` ≤ deg 7 — the deg-9 first attempt
with multiplier `(k+1)⁴(2k+e+2)` exceeds the normalizer budget; basis choice matters).
Remaining in (a): the *representation layer* — the cleared signed `c`-sum
(`√b(n,k)·2lcm³·c(n,k)` split pos/neg by kernel-parity, `HL` + heart_lcm terms) and the
`k`-induction assembling `collapsing_step` into the law statement.
**(b) DONE — all contiguity reductions PURE**
(`AperyCollapsing`, 15/0): §2 `b_welds` (`b_weld_n1/n2/mid` + `sqw_shift_n2`, pieces 1–3)
+ `gb_weld` (piece 4, the Ĝ-piece's crossed reduction
`(k+1)²(j+1−k)(j+k+2)(j+k+3)·C(j+2,k+1)C(j+k+1,k+1)² =
(j+1)²(j+2)²(j+k+1)·√b(j,k)·C(j+k+3,k+1)`, via `G1a`+`G1b`+`colA`+`colC`), §3 `T1`'s
two boundary evaluations (`t1_aL_weld` riding `aperyLead j = (2j+3)(17j²+51j+39)`;
`t1_ghat_weld`, both sides reduced to `2(j+2)(2j+3)(2j+1)·C(2j+2,j+2)C(2j,j)`);
**(c) DONE — R-NUM + R-BND are PURE
Lean theorems** (`NumberTheory/AperyNumeratorWZ.lean`, 13 PURE incl. the
machine-generated expansion/collection chain: R-NUM's single-`ring_nat` form exceeds the
reflective normalizer, so six per-term expansions + a pairwise collection chain compose
it; R-BND direct); (d) `sumTo` telescoping + R-NIL + the `W`-factoring welds; (e) induct
`zeta3Num=(n!)³A`.
The KEY FINDING below stands only as the **cap for the `b`-only language** — the
extension language dissolves it.

### Round-5 blueprint — the representation layer (designed 2026-07-02, not yet in Lean)

The cleared signed `c`-sum, ÷-free and parity-clean:

  * **Kernel term — LANDED** (`Zeta3Numerator` §kernel, 7/0 PURE): `ktw N n k m :=
    lcmUpTo(N)³·√b(n,k) / (m³·C(n,m)·C(n+m,m))` — a Nat for `1 ≤ m ≤ k ≤ n ≤ N`
    (`ktw_dvd` = `heart_lcm` at `(a,b) = (n−k,k−m)` + lcm-monotonicity; the global `2`
    of `2m³` cancels against the `2` of `2lcm³`); ÷-free characterization
    `ktw_mul_eq` (`(m³·C(n,m)·C(n+m,m))·ktw = lcm³·√b(n,k)`).
    **propext-trap additions** (avoid; NatHelper candidates): `Nat.dvd_trans` and
    `Nat.mul_assoc` leak `propext` in core — compose dvd-chains by explicit witness
    construction + `ring_nat` instead.
  * **Column reweighting** (next): `(k+1)²·ktw N n (k+1) m = (n−k)(n+k+1)·ktw N n k m`
    — from `ktw_mul_eq` × `sqw_shift_k` + `mul_left_cancel_pos`; needs `choose_pos`
    (`k ≤ n → 0 < C(n,k)`, a 3-line Pascal induction — belongs in `FLT/Binomial`).
  * **Parity split with clean bounds** (the weight column moves with `k`, so the
    parity-relative pair recursion must live at *fixed* weight column; simplest is
    absolute parity with `sumTo` and explicit counts):
    `kOdd N n k t := sumTo t (fun i => ktw N n k (2i+1))`, `kEven … (2i+2)`;
    at `k = 2t` the kernel has counts `(t,t)`, at `k = 2t+1` counts `(t+1,t)`; the
    `k`-induction alternates the two parity branches (two-step spiral), each step =
    one new `ktw` term + the column reweighting of all previous terms
    (`sumTo`-level: pointwise congruence + a `c·sumTo = sumTo (c·)` distribution).
  * **Cleared law (1)** (`×2·lcm³·n²(n−k)·√b(n,k)√b(n−1,k)`-couple): the harmonic
    `1/n³` keeps its own `(−1)^k`, so the law lands as **two** ℕ-statements
    (`k = 2t` / `k = 2t+1`), each `sub`-free by cross-arrangement, both consuming
    `collapsing_step` (§4) as the induction step and `HL_step`/`cube_dvd_lcm_cube` for
    the harmonic part.  Base `k = 0`: `sqw_zero` + `HL_step`.
  * Then (d): `U`'s cleared form = the same pair-representation at row `j+2` with the
    `b_welds`/`gb_weld` reductions; `sumTo_shift_eq` telescoping + `rnum_reduced` +
    `rbnd_reduced`/`t1_*_weld` + R-NIL (`choose_eq_zero_of_lt`) close `ΣU = 0`;
    (e) 2-step induction à la `zeta3Den_eq`.

## ★ KEY FINDING — no clean WZ certificate (re-read above: a cap for the b-only language; DISSOLVED in the extended language)

Unlike the denominator (clean `Ĝ(j,k)=−4k⁴(2j+3)(…)C(j+2,k)²C(j+k,k)²`), the
numerator/kernel certificates `cert_A`, `cert_K` are **harmonic-kernel-laden**
(messy rationals: `cert_K(6,2)=−24859/11760`, no fixed closed form).  Checked
(`numcert2.py`): even `cert_A − cert_B·c` (subtracting the denominator certificate
times the harmonic coefficient) is **still messy** — so there is no clean
certificate decomposition at all; the harmonic structure is irreducible to
certificate form.  The certificate-verification route used for `apery_recurrence`
does **not** transfer.

The K inhomogeneous recurrence must be proven by the **explicit Apéry algebraic
identities** — the kernel's partial-fraction telescoping across `n`
(`κ(n,k)` difference structure + `m³C(n,m)C(n+m,m)` ↔ `lcm` via `KeyDiv`/`Heart`).
This is the van-der-Poorten / Beukers algebraic route, a multi-session ∅-axiom
formalization (the hardest remaining piece of the whole ζ(3) program).  No CAS
shortcut exists — the next phase is the hand-derived kernel telescoping.

## Progress (2026-06-12, opened in Lean)

  * **`harmonic_part_recurrence` PURE** (`Zeta3Numerator.lean`): the cleared `H₃`
    part `(j+2)³HL(j+2)B(j+2)+(j+1)³HL(j)B(j)+ℓB(j)=aperyLead(j)HL(j+1)B(j+1)+ℓB(j+2)`
    (`HL ℓ n=Σℓ/i³`, `ℓ` a cube-multiple), from `apery_recurrence`×`HL(j+1)` +
    harmonic telescoping `HL_step`.  First numerator theorem.
  * **Abel form** (verified `numerator_plan` check): `K(n) = Σ_{m=1}^n δ(n,m)·
    Btail(n,m)`, `δ(n,m)=(−1)^{m−1}/(2m³C(n,m)C(n+m,m))`, `Btail(n,m)=Σ_{k≥m}b(n,k)`
    — a **single** sum (no inner `κ`).  Cleaner target for the K inhomog recurrence.
  * Kernel integrality `b(n,k)·lcm³/(m³C(n,m)C(n+m,m)) ∈ ℕ` reconfirmed (`heart_lcm`).

  **Next (the deep core)**: the K inhomogeneous recurrence via the Abel single-sum
  form — the explicit kernel telescoping (`δ`/`Btail` cross-`n` structure).  Then
  `A`-recurrence ⟹ `zeta3Num=(n!)³A` (induction, à la `zeta3Den_eq`), and the §4
  integrality assembly ⟹ the goal.

## Reusable (all PURE, done)
`apery_recurrence`, `B`, `zeta3Den_eq`, `heart_lcm`, `cube_dvd_lcm_cube`,
`keydiv`/`heart` (KeyDiv), `two_lcmCube_dvd_factCube`, `sumTo_shift_eq`,
the contiguity/`colrec`/`lowrec` machinery.
