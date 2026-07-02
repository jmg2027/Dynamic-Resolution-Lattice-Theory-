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

## ★ KEY FINDING — no clean WZ certificate (re-read above: a cap for the b-only language)

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
