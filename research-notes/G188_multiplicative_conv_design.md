# G188 — `mconv` (multiplicative twin of `conv`): the power-sum/Newton route, an honest ∅-axiom verdict

**Date**: 2026-06-03.  **Status**: design + feasibility note (Tier-1).  **No `.lean`
written.**  Companion to `G185_hadamard_linalg_program.md` (the determinant / Cayley–Hamilton
route).  This note investigates the *determinant-free* lead — power sums + Newton's identities
— asked for as the "multiplicative twin of `conv`", and renders a verdict on its viability over
`ℤ` under the ∅-axiom standard, then states the best fallback.

## 0. Context: where the gap sits

`Cauchy/CFiniteRing.lean` closes SUM-closure of C-finite ℤ-sequences via `conv` (coefficient
convolution = operator product).  `conv_annih_add`: if `P(Δ)` kills `s` and `Q(Δ)` kills `t`,
then `(P·Q)(Δ)` kills `s+t`; leading `1·1=1` keeps it monic (`conv_snoc`), so `cfiniteZ_add`
holds.  The composed-product roots there are the **union** `{αᵢ}∪{βⱼ}` and power sums **add**.

OPEN: the HADAMARD (pointwise) product `s·t`.  Its annihilator is the **composed product**
`P⊛Q` with roots the pairwise **products** `{αᵢ·βⱼ}` — a monic degree-`km` integer polynomial.
The classical computation is the resultant `Res_y(Q(y), yᵏ P(x/y))` = a `(k+m)×(k+m)` Sylvester
**determinant**.  `G185` plans exactly that determinant route (`DetN` → charPoly → Cayley–Hamilton
→ Kronecker companion).  This note asks: **can power sums + Newton's identities avoid the
determinant entirely, ∅-axiom over `ℤ`?**

## 1. Precise statement of `mconv` / the composed product

Coefficient lists are low-to-high in the `Δ`-power, as in `CFiniteRing` (monic = leading/last
coeff `1`).  Let `P` have roots (multiset) `{α₁,…,α_k}`, `Q` have `{β₁,…,β_m}`.

  - **Power sums** `pₗ(α) = Σᵢ αᵢˡ` (with `p₀ = k`), `pₗ(β) = Σⱼ βⱼˡ` (`p₀ = m`).
  - **KEY FACT (the lead).** For the composed product (roots `αᵢβⱼ`):
    `pₗ(α⊛β) = Σ_{i,j} (αᵢβⱼ)ˡ = (Σᵢ αᵢˡ)(Σⱼ βⱼˡ) = pₗ(α)·pₗ(β)` — power sums **multiply**
    (the multiplicative twin of "they add" for `conv`).  Cross-check `p₀(α⊛β) = km = p₀(α)p₀(β)`.
  - **Elementary symmetric** `eₖ` ↔ coefficients of the polynomial (signed): the composed product
    is `Πᵢⱼ (x − αᵢβⱼ) = Σ_{r} (−1)ʳ eᵣ xⁿ⁻ʳ`, `n = km`.

`mconv P Q` (the desired def) would be the three-stage pipeline:

```
P ──[coeffs → pₗ(α), l=1..n]──► pₗ(α)
Q ──[coeffs → pₗ(β), l=1..n]──► pₗ(β)
                  │ pointwise multiply (the KEY FACT)
                  ▼
              pₗ(α⊛β)  ──[Newton: pₗ → eᵣ → coeffs]──►  P⊛Q  (monic, degree n=km)
```

The annihilation target (mirror of `conv_annih_add`):

> `Annih P s → Annih Q t → Annih (mconv P Q) (fun n => s n · t n)`

with `(mconv P Q).getLastD 0 = 1` (monic), so `cfiniteZ_mul` follows exactly as `cfiniteZ_add`
followed from `conv_annih_add`.

## 2. The ÷k obstruction — is it fatal? (the central feasibility question)

**Newton's identities** (both directions) intertwine `pₗ` and `eᵣ`:

```
forward  (e → p):   pₗ = e₁pₗ₋₁ − e₂pₗ₋₂ + … + (−1)ˡ⁻¹ l·eₗ          ← note the bare l·eₗ
backward (p → e):   eₖ = (1/k)·( e_{k−1}p₁ − e_{k−2}p₂ + … + (−1)ᵏ⁻¹ pₖ )  ← explicit 1/k
```

Both carry the integer `k`/`l` **multiplying** the term you want to isolate, so solving for it
needs a **division by `k`**.  Over `ℤ` with no `Classical`/no field, you cannot write `÷k` as a
total operation that the prover trusts to be exact.

**Is the division always exact?**  YES — mathematically.  The composed product is monic with
integer coefficients (it is `det(xI − A_P⊗A_Q)`, a polynomial in the integer entries of the
Kronecker product of the two companion matrices; equivalently a resultant, integral by Gauss's
lemma since `P,Q` are monic integer).  Its power sums `pₗ = trace((A_P⊗A_Q)ˡ)` are integers.  So
each `eᵣ` extracted by backward-Newton **is** an integer; the `÷k` lands exactly.

**Is the exactness elementarily ∅-axiom-provable?**  This is where the route **breaks**.  To use
backward-Newton in Lean over `ℤ` you must, at each step `r=1..n`, prove
`k ∣ (e_{k−1}p₁ − … + (−1)ᵏ⁻¹ pₖ)` and then *take the quotient*.  Three sub-problems, each a
genuine obstruction under the ∅-axiom / no-Mathlib / no-`Int.div`-lemmas regime:

  1. **`Int` division is not in the kit.**  `Meta/Int213` builds the *ring* (`add,mul,neg,sub`,
     `ring_intZ`, `powInt`); there is **no** `Int.ediv`/`tdiv` lemma layer, no `Dvd` API, no
     `Int.ediv_mul_cancel`-style cancellation that is `propext`/`Classical`-free (core `Int`
     division lemmas pull `propext`).  Building a ∅-axiom exact-division layer on `ℤ` is itself a
     sub-project of unknown size and arguably the wrong shape (division is not a 213-native
     readout — cf. `integers_as_difference_lens`: `ℤ` is the *difference*-Lens readout group; a
     *quotient* group is a different, heavier Lens).
  2. **Proving `k ∣ (…)` requires the symmetric-function combinatorics** that *is* Newton's
     identity — i.e. you must prove the integrality theorem (the alternating multinomial sum is
     divisible by `k`) to even define the next coefficient.  That is the classical
     "Newton's-identity-with-integrality" theorem, ∅-axiom, over `ℤ`, by induction on the partition
     lattice / Waring formula.  No part of the repo touches symmetric-function theory; this is a
     multi-hundred-line build *before* any sequence statement.
  3. **The division is interior to the recursion**, so it is not a one-off: every degree-`r` step
     re-incurs (1)+(2).  You cannot defer it.

**VERDICT on the power-sum/Newton route**: ✗ **Not viable as the ∅-axiom path**, *not* because the
mathematics fails (it is correct and the divisions are exact) but because making the divisions
**provably exact in Lean over `ℤ` with zero axioms** requires (a) an `Int` exact-division layer
the repo deliberately lacks and (b) the integral Newton's-identity theorem (symmetric-function
combinatorics) — together a heavier build than the determinant route it was meant to avoid, and
philosophically off-grain (quotient, not difference).  The "÷k is exact" fact is true but is the
*conclusion* of the hard theorem, not a shortcut around it.

### 2a. Can the ÷k be *reformulated away*?  (the honest search for a clean division-free twin)

I checked the standard escape hatches; none yields a clean ∅-axiom `mconv`:

  - **Forward-only, scaled coefficients.**  The forward identity `pₗ = e₁pₗ₋₁ − … + (−1)ˡ⁻¹ l·eₗ`
    is division-free *in the `e→p` direction*.  But we need `p→e` (we *have* the `pₗ(α⊛β)` and
    *want* the coefficients).  Carrying `l!·eₗ` (clearing all denominators) is division-free to
    *compute*, but then the final list is `n!`-scaled and **not monic** (leading term `n!`, not
    `1`) — `CFiniteZ` needs monic, so you must divide by `n!` at the end: the obstruction returns,
    concentrated.
  - **Generating functions / log-derivative.**  `Σ pₗ zˡ = −z·P'(z)/P(z)` (reversed).  The
    composed-product GF is the Hadamard product of the two such series — but recovering
    coefficients from `Σ pₗ zˡ` is `exp(∫ …)`, i.e. `1/k` again.  No gain.
  - **`p`-only annihilation.**  Could we annihilate `s·t` *directly from power sums* without ever
    forming the coefficient list?  The power sums are the traces of `Mˡ`, `M = A_P⊗A_Q`; the
    recurrence they satisfy *is* the char poly — so "use the `pₗ`" is "use the char poly", which
    is the determinant route.

So there is **no clean division-free reformulation that still lands a monic ℤ list cheaply**.
The one genuinely division-free, ∅-axiom-friendly route is **not** Newton at all — see §3.

## 3. The genuinely viable ∅-axiom route (recommended): division-free, determinant-free **finite-orbit closure**

The power-sum lead pointed at the right *structure* (the Kronecker companion `M = A_P⊗A_Q`) but
the wrong *extraction* (Newton).  There is a third route that is **division-free, determinant-free,
Cayley–Hamilton-free**, and matches `CFiniteRing`'s existing grain (`shiftSum`, finite orbit):

**The km cross-products are a shift-closed spanning set.**  As `G185 §"The mathematics"` notes:
with `s(n+k)=Σ aᵢ s(n+i)`, `t(n+m)=Σ bⱼ t(n+j)`, the `km` products
`u_{pq}(n) = s(n+p)·t(n+q)` (`p<k, q<m`) satisfy `E u_{pq} = u_{p+1,q+1}` and reduce at the
boundary by `a,b` — entirely **ring operations, no division**.  Hence `V(n)=(u_{pq}(n))` obeys
`V(n+1)=M·V(n)`, `M` an explicit `km×km` **integer** matrix, and `s·t = u₀₀ = V`'s first
component.

The *abstract* C-finiteness of `s·t` then needs only: **a shift-orbit lying in a fixed
`km`-dimensional ℤ-span is C-finite.**  That is the "finite Δ-orbit ⟹ recurrence" shape that
`CFiniteZ` *already is*, but to get it for `s·t` you need one general lemma the repo lacks:

> **(LD)** *Any `D+1` vectors in `ℤ^D` admit a nontrivial integer linear dependence.*

`(LD)` is the integer pigeonhole-for-linear-dependence.  `Lib/Math/Pigeonhole.lean` has the
*set* pigeonhole (`no_inj_lt`); `Linalg213/Rank` has only **concrete bounded** dependencies
(`e0_e1_LI_bounded`), not the general existence theorem.  Crucially, `(LD)` gives a dependence
`Σ cᵢ V(i)=0` that is in general **non-monic** (leading `c` need not be `±1`) — which is exactly
`G185 §"The crux — monic"`'s complaint.  **`CFiniteZ` requires monic.**

So the finite-orbit route is division-free and determinant-free **but lands a non-monic
recurrence**, and `CFiniteZ`/`ShiftRecZ` as defined demand monic (leading coeff `1`).  Two ways
out, in increasing soundness:

  - **(M1) Weaken/extend the C-finite def to allow a monic-up-to-leading-unit, or a non-monic
    leading nonzero ℤ-recurrence, and prove it equivalent.**  Over `ℤ`, "C-finite" is genuinely
    "monic ℤ-recurrence" (a non-monic `c_K·s(n+K)=lower` with `c_K≠±1,0` is *not* a `ℕ→ℤ`
    recurrence you can iterate forward without dividing).  So you **cannot** freely drop monic;
    the leading coefficient must be inverted, and over `ℤ` that needs `c_K = ±1`.  This is the
    same wall.
  - **(M2) Recover monic via the char poly of `M`** = the determinant route again.

**Net:** the division-free finite-orbit argument cleanly proves "`s·t` satisfies *some* nonzero
ℤ-recurrence of order ≤ `km`" (a non-monic `ShiftRecZ`-like statement), but **monic integrality —
the actual `CFiniteZ` requirement — provably needs the characteristic polynomial = a
determinant.**  This is the structural reason `G185` chose the determinant: *over `ℤ` there is no
escape from `det` to reach monic.*  The power-sum route hides the same `det` inside "the `pₗ` are
the trace recurrence = char poly".

## 4. Recommended design — defer to the determinant route, with one cheap independent win

Given §2–§3, the honest design recommendation is:

  1. **Do NOT build `mconv` via Newton.**  Record it as investigated-and-rejected (this note).
  2. **Proceed with `G185`'s determinant route** (`DetN` → `charPoly` → integer Cayley–Hamilton →
     Kronecker companion → `cfiniteZ_mul`).  It is the only path to *monic* over `ℤ`.
  3. **Bankable independent win that the power-sum lead *does* cleanly give** (∅-axiom, no `det`):
     the **power-sums-multiply identity as a sequence theorem**, which is the trace/Newton-sum
     half *without* the inverse extraction.  Concretely, for the special case where one factor is
     a pure geometric `cⁿ` this is already `CFiniteRing.cfiniteZ_geomScale`.  The next cleanly
     closable corner (no determinant) is **`s·t` when one factor has all distinct integer roots
     given explicitly** (then the composed product can be *built by `conv`-style root-pair
     adjunction*, monic by construction — see §5), sidestepping both Newton and `det`.

### Effort/risk on the recommended determinant route (refining G185)

  - **Lines / sessions**: ~1000+ lines, 3–5 sessions (unchanged from `G185`).  Dependencies:
    `Linalg213/DetN.lean` (exists, 2 sanity lemmas) needs **multilinearity + alternating + Laplace
    cofactor** (Phase A, the hard sign-bookkeeping induction), then `charPoly`, then integer
    **Cayley–Hamilton** (Phase C, the genuine theorem).
  - **Hardest lemma**: integer Cayley–Hamilton `χ_M(M)=0` via the adjugate identity
    `M·adj M = det M·I` — multilinearity-heavy, ∅-axiom (no `Matrix` Mathlib API).  This single
    theorem is the bulk of the risk.
  - Uses: `Meta/Int213` (`ring_intZ`, `add/mul/neg`), `powInt`; **`Linalg213/DetN.lean`**;
    NOT `NewtonGregory.bsum` (different sum), NOT `Combinatorics/Binomial` (no binomials here).

## 5. Best *cheap* fallback to bank now (recommended first commit, ∅-axiom, no `det`, no Newton)

The one corner that is **monic by construction and division-free**: build the composed product by
**incremental root-pair adjunction** for a factor presented with explicit integer roots.

If `Q = Π_j (x − rⱼ)` with the `rⱼ : ℤ` given (e.g. `t` a sum of integer geometrics `Σ cⱼ rⱼⁿ`),
then `P⊛Q = Π_j P(x; scaled by rⱼ)` where `P` scaled by `r` has roots `{r·αᵢ}`.  Scaling a monic
poly's roots by `r` is the **division-free, monic-preserving** map
`coeffScale r P = [P₀, r·P₁, r²·P₂, …]` reversed appropriately (`Pᵢ ↦ rⁿ⁻ⁱ Pᵢ`, leading stays
`1`).  Then `P⊛Q = conv`-fold of the `coeffScale rⱼ P` over `j` — **all `mul`/`powInt`, monic by
`conv_snoc`** (leading `1·1·…=1`), zero division, zero determinant.

  - **`def coeffScale (r : Int) (P : List Int) : List Int`** — `Pᵢ ↦ rᵈ⁻ⁱ·Pᵢ` (degree `d`).
    Annihilation: if `P(Δ)` kills `s` then `coeffScale r P` (in the *shift* algebra) relates to
    `rⁿ·s` via `applyShift_smul`/`geom_shiftSum` (already in `CFiniteRing §12`).
  - **`def mconvRooted (P : List Int) (rs : List Int) : List Int`** = `rs.foldr (conv ∘ coeffScale·P)`.
  - **Key lemma** (proof sketch): induction on `rs`, base `conv`-identity, step via
    `cfiniteZ_geomScale` (the `rⁿ·s` corner already closed) + `cfiniteZ_add` — so `s·t`
    for `t = Σ cⱼ rⱼⁿ` reduces to a `conv`/`geomScale`/`add` combination **already proven**.
    This is genuinely closable in **~150–250 lines, 1 session**, ∅-axiom, and covers the
    physically common case (Hadamard product against an explicit-integer-spectrum sequence:
    `fib·2ⁿ`, `n²·3ⁿ + 5ⁿ`, etc.) without any of the §2–§4 machinery.  Hardest lemma there:
    `coeffScale`'s annihilation in the shift algebra, ~40 lines, analogous to `geom_shiftSum`.

This fallback is the recommended **next commit**: it banks the realistically-reachable slice of
the Hadamard frontier with existing tools, while the full general (irrational/repeated-root)
case waits on `G185`'s determinant build.

## 6. Verdict summary

  - **`mconv` via power sums + Newton (the asked lead): ✗ not ∅-axiom-viable.**  The mathematics
    is correct and the `÷k` divisions are exact, but proving exactness in Lean over `ℤ` with zero
    axioms requires (i) an `Int` exact-division layer the repo deliberately omits (and which is
    off-grain — `ℤ` is the *difference* Lens, not a quotient) and (ii) the integral
    Newton's-identity / symmetric-function theorem — together heavier than the determinant route
    it was meant to dodge.  No clean division-free reformulation survives (forward-only gives a
    non-monic `n!`-scaled list; GF/log-derivative re-introduces `1/k`; "use the `pₗ` directly" *is*
    the char poly).
  - **Why no shortcut exists**: over `ℤ`, reaching a **monic** annihilator (which `CFiniteZ`
    requires) provably needs the **characteristic polynomial = a determinant**.  Every
    determinant-free route (finite-orbit pigeonhole `(LD)`, power sums) cleanly delivers only a
    *non-monic* ℤ-recurrence; monic integrality is exactly the content `det` supplies.
  - **Recommended path**: (1) bank the cheap **`mconvRooted`/`coeffScale` fallback** (§5,
    ~150–250 lines, 1 session, reuses `cfiniteZ_geomScale`+`cfiniteZ_add`) covering explicit
    integer-spectrum Hadamard products; (2) for the general case, proceed with **`G185`'s
    determinant → Cayley–Hamilton → Kronecker** program (~1000+ lines, 3–5 sessions; hardest
    lemma: integer Cayley–Hamilton via the adjugate).
  - **Net**: the power-sum lead is *structurally* right (it correctly identifies `M = A_P⊗A_Q`)
    but is not an extraction shortcut; it is the determinant in disguise.

## Anchors

  - This note: `research-notes/G188_multiplicative_conv_design.md`.
  - Companion (determinant program): `research-notes/G185_hadamard_linalg_program.md`.
  - Sum-closure twin: `lean/E213/Lib/Math/Cauchy/CFiniteRing.lean` (`conv`, `conv_annih_add`,
    `conv_snoc`, `cfiniteZ_add`; geometric-factor corner `cfiniteZ_geomScale`, `geom_shiftSum`).
  - Determinant seed: `lean/E213/Lib/Math/Linalg213/DetN.lean` (`det`, `minor`, `cofSum`).
  - Ring kit: `lean/E213/Meta/Int213/{Core,PolyIntM}.lean` (`ring_intZ`, `powInt`, `powInt_add`).
  - `ℤ`-as-difference-Lens (why quotient/division is off-grain):
    `theory/essays/integers_as_difference_lens.md`, `seed/AXIOM/06_lens_readings.md §6.7`.
  - Finite-sum infra (not reused by `mconv`, noted for completeness):
    `lean/E213/Lib/Math/Cauchy/NewtonGregory.lean` (`bsum`), `Combinatorics/Binomial.lean`.
