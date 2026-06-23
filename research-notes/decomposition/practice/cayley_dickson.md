# Decomposition: the Cayley–Dickson tower (iterated doubling; residue = the law lost each step)

*213-decomposition of "ℝ → ℂ → ℍ → 𝕆 → … / division & composition algebras", per `../README.md`. Ties
**both** invariants: the doubling uses conjugation (`conj`, the `q=±1` involution, Invariant B) and the
surviving structure is the **multiplicative norm character** `N(xy)=N(x)N(y)` (Invariant A, `×↦·`).*

## The decomposition

- **Construction `C`** — **iterated doubling**: `α ↦ CDDouble α` (`Meta/Algebra213/CDDouble.lean:44`), a pair
  `(re, im) : α × α` with the twisted product using conjugation.  Run from `ℝ`: `ℝ → ℂ → ℍ → 𝕆 → 𝕊 → …`, the
  carrier dimension doubling each step (`1,2,4,8,16,…`).  Not five "number systems" — **one construction at
  five depths**.
- **Reading `L`** — **conjugation** `conj : CDDouble α → CDDouble α` (`CDDouble.lean:63`), the involution
  `(re,im) ↦ (conj re, −im)`.  It is the `q=±1` involution: its **fixed** space is the reals/scalars
  (`q=+1`, `trace a = a + conj a`), its **anti-fixed** space the imaginaries (`q=−1`), which **doubles each
  step**.  `conj` defines the **norm** `N(x) = x · conj x` (`self_mul_conj`, the `q=+1` "length²") and the
  trace (`conj_eq : conj a = ofInt(trace a) − a`, `CDDoubleMoufang.lean:70`).
- **Residue `⊕`** — the **algebraic law lost at each doubling**, monotonically:
  - `ℝ → ℂ`: lose the **order** (ℂ is not ordered);
  - `ℂ → ℍ`: lose **commutativity**;
  - `ℍ → 𝕆`: lose **associativity** (only *alternativity* survives);
  - `𝕆 → 𝕊`: lose **alternativity** *and* the multiplicative norm — **zero divisors** appear, the
    division/composition property dies.
  Each level's residue is exactly the law the previous level still had.

## Re-seeing the theorems

**What SURVIVES the doubling is the content the CD library proves ∅-axiom** — the surviving laws are the
`q=+1` "kept" residue-complement at each level:
- **Alternativity + flexibility** (survive through `𝕆`): `CDDoubleAlternative.lean:26 cd_alt_left`,
  `:111 cd_alt_right` (`x·(y·y) = (x·y)·y`), `:131 cd_flexible` (`(a·b)·a = a·(b·a)`). **PURE (3/0).**
- **The multiplicative norm character** (composition algebra, Invariant A): `CDDoubleMoufang.lean:80
  diag_collapse` — `(x·y)·(conj y·conj x) = ofInt(normSq y · normSq x)`, i.e. **`N(xy) = N(x)·N(y)`**, the
  `×↦·` character on norms; `:119 hurwitz_cross` (the Hurwitz cross-cancellation that makes it work). **PURE
  (23/0).**

So "ℝ, ℂ, ℍ, 𝕆 are four division algebras" is the statement that the **norm character `×↦·` survives four
doublings** — and **Hurwitz's theorem** (normed division algebras exist only in dimensions `1,2,4,8`) is the
**`q`-tagged termination of the tower**: the doubling iteration runs, and the `×↦·` norm character holds
(`q=+1`) at depths `0–3` and **fails** (`q=−1`, zero divisors) at depth `4` (`𝕊`).

## Revelation (collapse + forcing)

**Collapse — the four number systems are one doubling, four resolutions.**  ℝ/ℂ/ℍ/𝕆 are not four objects
related by inclusions; they are `⟨double | conj⟩` at depths `0,1,2,3`, and the *differences between them are
the residues* (the lost laws), exactly as `prime_factorization.md`'s "multiplicative vs additive = one
construction, two readings".  The tower is the construction; conjugation is the reading; the lost law is the
residue.

**Forcing — the tower terminates where the `×↦·` character breaks, and that is a theorem of the surviving
laws.**  The CD library does not assume associativity fails; it **proves what holds** — alternativity
(`cd_alt`), flexibility, the Moufang/Hurwitz composition (`diag_collapse`, `hurwitz_cross`) — and these are
exactly the laws that *barely* survive to `𝕆`.  The next double cannot keep `N(xy)=N(x)N(y)` (the cross-terms
`hurwitz_cross` cancels need alternativity, which is now gone), so composition fails: **the `q=+1` survival
of the norm character is what bounds the tower at dimension 8.**  Both invariants meet here: `conj` (the
`q=±1` involution, Invariant B) drives the doubling, and the multiplicative norm (Invariant A) is what the
doubling can preserve only finitely.

## Verified Lean anchors (file:line:theorem — grep-confirmed, scans this session)

- `Meta/Algebra213/CDDouble.lean:44 CDDouble` (the doubling structure), `:63 conj` (the involution).
  **PURE (2/0).**
- `Meta/Algebra213/CDDoubleAlternative.lean:26 cd_alt_left`, `:111 cd_alt_right`, `:131 cd_flexible` — the
  surviving alternativity/flexibility (the `q=+1` kept laws through `𝕆`). **PURE (3/0).**
- `Meta/Algebra213/CDDoubleMoufang.lean:80 diag_collapse` (`N(xy)=N(x)N(y)`, the `×↦·` norm character),
  `:119 hurwitz_cross` (Hurwitz cross-cancellation), `:70 conj_eq` (`conj a = ofInt(trace a) − a`). **PURE
  (23/0).**
- `Meta/Algebra213/CDDoubleFlexible.lean:79 left_assoc_conj`, `:90 right_assoc_conj`, `:103 conj_sandwich`
  — the conjugation-associativity fragments (associativity survives *only* against a conjugate).

## BUILT vs ABSENT

- **BUILT (∅-axiom):** the doubling construction (`CDDouble`), conjugation/trace/norm, and the surviving
  laws through `𝕆` — alternativity, flexibility, the Moufang/Hurwitz norm-multiplicativity (`diag_collapse`,
  the `×↦·` character).  This is the `q=+1` "kept" side at depths 0–3, ∅-axiom.
- **ABSENT (predicted-not-built):** the **named tower terminus** — a Lean statement "`𝕊` (depth 4) has zero
  divisors / the norm character fails" (the `q=−1` residue at depth 4), and **Hurwitz's theorem** packaged
  as "normed division algebras ⟺ dim ∈ {1,2,4,8}".  The corpus builds the *surviving* laws (the `q=+1`
  witnesses); the *failure* at depth 4 (the predicted residue) is not yet a theorem — the same BUILT-survivor
  / ABSENT-terminus pattern as the other towers.

## Touches the model?

**No new primitive — both invariants at once.**  The construction is iterated doubling; the reading is `conj`
(the `q=±1` involution, Invariant B, anti-fixed imaginaries doubling each step); the surviving structure is
the multiplicative norm `N(xy)=N(x)N(y)` (Invariant A, `×↦·`).  New datum: the CD tower is the cleanest place
**both invariants are load-bearing in one object** — `q=±1` conjugation *drives* the doubling, and the `×↦·`
norm character is *what the doubling preserves only to depth 3* (Hurwitz), so the residue (lost law) and the
tower's termination are two readings of where the `×↦·` character finally breaks.
