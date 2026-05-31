# G155 — HolonomicReal: internalising the modulus gate into type architecture

**Date**: 2026-05-31. **Status**: design spec + Lean 4 sketches (NOT yet compiled).
**Depends on**: completeness arc (`completeness_without_completeness.md`),
`Real213/{AbCutSeq,EulerCut,PiCut,PhiAsCut}`, `Cauchy/{DivergenceLadder,DepthTower,
DepthOrdinal,DepthPRecursive}`, `Analysis/CauchyCompleteValid`, `G154`.

This note records a proposed architecture (originator-driven) for turning two
*formal-overhead* properties of the completeness arc into type structure and
computer-algebra automation.  It keeps three honest scope corrections up front, then
specs three axes with code sketches.

## Scope corrections (read first — the proposal's framing carried three errors)

1. **Liouville has NO finite ordinal coordinate.**  The earlier framing "Liouville:
   ω+d" is the retracted claim.  `DepthDoubleExp.dexp_not_const` proves the opposite:
   `c^{k!}` is a fixed point of every `ratioN`, so it has *no* finite `(h,d)` and
   sits at depth ∞.  The finite-coordinate reals are exactly the `c^{poly}` /
   P-recursive class.  Any HolonomicReal architecture covers precisely that class and
   **excludes** Liouville-type reals by construction — that exclusion is the point,
   not a gap.

2. **depth = P-recursive rank is (C), not (L).**  The depth values φ 1 / e 3 / π 6
   are Lean-checked; their identification with the holonomic/P-recursive rank is a
   classical bridge, not yet a ∅-axiom theorem (next-target B).  So "perfectly mapped
   the internal structure of transcendentals" overstates: the *lattice points* are
   mapped; the *rank = depth* law is the brick still to lay.

3. **Descent termination is proved once, not per operation.**  `DepthOrdinal.lex_wf`
   / `no_infinite_descent` establish well-foundedness of `ℕ×ℕ` lex *once*; every
   downstream use *applies* it.  What is per-instance is **computing the coordinate**,
   not re-proving termination.  So `solve_descent` (Axis 2) is a *convenience*
   automation (parse → compute coordinate → apply the existing `lex_wf`), not a
   soundness device.  Framing it as "removing a manual termination proof" is wrong.

## The reach, stated correctly (this strengthens the proposal)

The holonomic class is **broader than the regular-continued-fraction class**.  A real
whose convergents satisfy a polynomial-coefficient recurrence is holonomic regardless
of whether its CF is arithmetic.  So:

  - φ, √2 — order-2 *constant*-coefficient (autonomous, `det=1`): holonomic, depth 1.
  - e — coeff `n+1` (degree 1): holonomic, depth 3.
  - **π via Wallis** — cross-det coeff degree 4: holonomic, depth 6.  π's *CF* is
    irregular, but its *Wallis* recurrence is P-recursive, so π is plausibly **inside**
    the holonomic class and its gate is dischargeable through Wallis (target B, π case).
  - Liouville, depth ∞ — genuinely non-holonomic; the gate stays.

So HolonomicReal discharges the modulus hypothesis for *every finite-depth real*,
which is the whole point of the arc — only the depth-∞ pathology keeps a hypothesis.

---

## Axis 1 — `HolonomicReal`: bundled certificate, transparent unconditional API

**Idea.**  Bundle (i) the P-recursive recurrence data, (ii) the `CertifiedModulus`
*derived from* that data, and (iii) the decision procedure `cut`, into one structure.
The modulus is then a *constructed field*, not an external hypothesis, so the public
API behaves like an unconditional real while statically carrying its convergence-rate
certificate.

This is the typed form of next-target B: instead of `EulerCut.toCauchy (modulus :
hypothesis)`, the modulus is `Holonomic.certifiedModulus hol`, a closed term.

```lean
/-- A P-recursive (holonomic) recurrence of order `r` with polynomial coefficients
    `p i : Nat → Int`: the convergent data `s` satisfies `Σ_{i<r} p i n · s (n+i) = 0`.
    Polynomial coefficients are stored by their degree-bounded value-functions. -/
structure Holonomic where
  order  : Nat
  coeff  : Fin order → (Nat → Int)
  cdeg   : Fin order → Nat                 -- degree bound of each coeff, drives modulus
  init   : Fin order → Int

/-- The convergence-rate certificate DERIVED from holonomic data: an explicit
    `Nat → Nat → Nat` modulus plus the proof that it bounds the cut's tail.
    `certifiedModulus` is a pure function of `hol` (no LEM): a P-recursive tail with
    known polynomial coefficients has a computable ratio bound, hence a computable
    modulus.  This is the field that, once proven, discharges the hypothesis. -/
structure CertifiedModulus (cut : Nat → Nat → Bool) where
  N         : Nat → Nat → Nat
  certified : ∀ m k, IsModulusAt cut N m k        -- the bound, eager, ∅-axiom

/-- The headline type: a real that is *unconditional at the API* because its modulus
    is a constructed field, not an assumption.  Coerces to the plain `ValidCut`
    interface; downstream code never sees a modulus hypothesis. -/
structure HolonomicReal where
  hol   : Holonomic
  cut   : Nat → Nat → Bool
  valid : ValidCut cut
  cert  : CertifiedModulus cut
  -- INVARIANT (the brick to prove): cert is GENERATED from hol, i.e.
  --   cert = Holonomic.toCertifiedModulus hol cut valid
  derived : cert = Holonomic.toCertifiedModulus hol valid

/-- The generator: holonomic data ⟹ certified modulus.  THIS function is the
    ∅-axiom content of the whole axis (target B).  For e: order 2, coeff `n+1`; the
    tail ratio `≤ 1/(n+1)` gives `N m k = <explicit>`.  Proven per coefficient-shape,
    then instances (e, π-via-Wallis) are thin applications. -/
def Holonomic.toCertifiedModulus (hol : Holonomic)
    (valid : ValidCut cut) : CertifiedModulus cut := by
  sorry  -- DESIGN SKETCH ONLY; the real proof is target B, per coeff-degree class

/-- Coercion: a HolonomicReal IS a Real213 cut, with no modulus exposed. -/
instance : CoeTC HolonomicReal Real213 := ⟨fun h => ⟨h.cut, h.valid⟩⟩
```

**Honest status.**  `toCertifiedModulus` is the unproven core; everything else is
packaging.  The packaging is cheap; the brick is proving the explicit modulus per
coefficient-degree class.  Start with the autonomous case (`order = 2`, constant
coeff = φ/√2, already done as `PhiAsCut`) then degree-1 (e) then degree-4 (π/Wallis).

---

## Axis 2 — holonomic closure algebra + `solve_descent` (convenience automation)

**Part A — closure algebra (real ∅-axiom library).**  Holonomic sequences are closed
under `+` and `×`, with rank (recurrence order, ≈ depth) bounded:

```lean
namespace HolonomicReal
/-- Sum of holonomic reals is holonomic; order ≤ sum of orders. -/
theorem rank_add (A B : HolonomicReal) :
    (A + B).hol.order ≤ A.hol.order + B.hol.order := by sorry
/-- Product; order ≤ product of orders (classical: order·order bound). -/
theorem rank_mul (A B : HolonomicReal) :
    (A * B).hol.order ≤ A.hol.order * B.hol.order := by sorry
end HolonomicReal
```

These are the classical holonomic closure bounds (Zeilberger/Stanley), formalised
∅-axiom.  With them, the ordinal coordinate of a *composite* transcendental is bounded
by the base coordinates' combination — no new descent reasoning needed, just the
arithmetic of the bounds plus the *already-proven* `lex_wf`.

**Part B — `solve_descent` macro (convenience, NOT soundness; hazard-flagged).**
The tactic parses the holonomic coefficient data, computes the `(h,d)` coordinate via
`diffN`/`liftK`, and discharges the termination goal by *applying* `DepthOrdinal.
no_infinite_descent`.  It removes boilerplate, not a proof obligation.

```lean
/-- Compute coordinate then apply the once-proven well-order.  Sketch. -/
macro "solve_descent" : tactic => `(tactic|
  ( -- 1. reflect the holonomic coeffs into (h,d) by structural computation
    -- 2. `exact DepthOrdinal.no_infinite_descent <computed coord>`
    first
      | exact DepthOrdinal.no_infinite_descent _ _
      | fail "solve_descent: coordinate not finite (depth ∞? check holonomicity)" ))
```

**PURITY HAZARD (must respect, per hygiene notes).**  A macro that emits proof terms
must NOT route through `decide`/`omega`/`native_decide` (they pull `propext`).  The
coordinate computation must reduce to structural `Nat.lt` lemmas and the explicit
`lex_acc` term, or the generated proof is axiom-dirty.  `solve_descent`'s acceptance
test is `scan_axioms` on a theorem closed by it, not just that it closes the goal.

---

## Axis 3 — automatic reals + lazy certificate (speculative; layer-confusion flagged)

**Part A — automaton reals (genuine extension).**  Beyond P-recursive, sequences
generated by a finite state-transition (automatic / morphic sequences) are still
*computable*, so a modulus is constructible from the automaton.  Typeclass:

```lean
/-- A real whose convergent data is produced by a finite-state transition (matrix
    product / substitution rule).  Computable ⟹ modulus constructible. -/
class AutomatonReal (α : Type) where
  states  : Type
  step    : states → states            -- transition (or a Fin n → matrix)
  readout : states → (Nat × Nat)       -- convergent (num, den)
  start   : states
  -- modulus derived from the transition's contraction rate
  modulus : Nat → Nat → Nat
  certified : ∀ m k, IsModulusAt (cutOf readout) modulus m k
```

This is a real direction: it pushes the unconditional class from holonomic to
automatic, both being "modulus = function of finite generating data".

**Part B — "lazy certificate thunk": LAYER CONFUSION, corrected reading.**
The proposal asks to *defer* the complexity binding to evaluation time.  This
conflates Lean's two layers:

  - **Values** can be deferred — Lean has `Thunk`, and the convergent data can be a
    lazily-forced stream.  Fine, compiles, purity-neutral.
  - **Certificates (proofs) CANNOT be deferred.**  Lean is total; the proof that a
    modulus bounds the tail must exist in the term at type-check time, or the type is
    not inhabited.  There is no "evaluate-time-generated proof".

The only purity-safe reading of "lazy certificate" is: the certificate is a
**function** `(prec : Nat) → Σ data, Proof (data bounds prec)` — the *type* is eager
(always present, guaranteeing a certificate for every precision), only the
*evaluation* of each prefix is on demand.

```lean
/-- Purity-safe "lazy certificate": an eager dependent function, lazily evaluated.
    NOT codata, NOT `partial`, NOT `Stream` via `Quot` (those break ∅-axiom). -/
def CertStream (cut : Nat → Nat → Bool) :=
  (prec : Nat) → { N : Nat // IsModulusAtPrec cut N prec }
```

Avoid: coinductive `Stream`, `partial def`, `Quot`-based laziness — each risks the
purity contract.  Lazy *value* computation via `Thunk` is the only deferral that
stays ∅-axiom.

---

## Build order (if pursued)

1. **Axis 1, autonomous case** — wrap `PhiAsCut` as a `HolonomicReal` (order 2,
   constant coeff); `toCertifiedModulus` is the already-proven `N = 2k`.  Proves the
   architecture end-to-end on a closed instance.
2. **Axis 1, degree-1** — e: discharge `EulerCut`'s hypothesis via the `n+1` coeff
   (this IS target B, e case).
3. **Axis 1, degree-4** — π via Wallis (target B, π case); confirms the holonomic
   class contains π.
4. **Axis 2A** — `rank_add` / `rank_mul` closure library.
5. **Axis 2B** — `solve_descent`, with a `scan_axioms` acceptance gate.
6. **Axis 3** — only after 1–5; automaton typeclass + `CertStream` (eager-type form).

The honest headline: this internalises the gate **for the finite-depth (holonomic,
then automatic) class** — which is exactly the class the arc maps — and leaves the
depth-∞ pathology explicitly outside, where it belongs.
