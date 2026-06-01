import E213.Lib.Math.Cauchy.DepthDoubleExp

/-!
# DepthOmegaTower — the depth-`r` tower coordinate is an ordinal below `ω^ω`

`DepthOrdinal` proved the two-axis coordinate `(h, d)` is an ordinal below `ω²`:
the lexicographic order on `Nat × Nat`, read as `ω·h + d`, is a well-founded strict
linear order.  `DepthExponentRecursion` then showed the axis tower is a self-similar
recursion — resolving a value `c^{eₙ}` resolves its exponent `eₙ` one axis down, so
**value-height = 1 + exponent-height** — and `DepthDoubleExp` proved each exponential
layer is genuinely new (`ratioN` cannot cross one layer: `dexp_not_const`).

This file closes the ordinal side of that recursion.  A depth-`r` tower of axes has
a coordinate that is an `r`-fold nested lexicographic product `Coord r` — read as a
base-`ω` polynomial `ω^{r-1}·a₀ + … + ω·a_{r-2} + a_{r-1}`, an ordinal below `ω^r`.
The headline `coord_wf` proves this is **well-founded for every `r`**: the whole
`ω^ω` ladder, level by level (`Coord 2` is exactly `DepthOrdinal`'s `ω²`).  So "the
infinite handled by a finite reference, iterated" terminates at every finite tower
height — `coord_no_infinite_descent`.

The positive content matching the recursion:

  * `coord_layer_dominates` — adding one tower level *multiplies the rank by `ω`*:
    a strictly larger leading coefficient outranks the entire lower tower
    (`ω^r·(a+1) > ω^r·a + ‹anything below ω^r›`).  This is the ordinal shadow of
    "each exponential layer is a new axis" (`DepthDoubleExp`).
  * `expTower` / `expTower_succ` — the `r`-fold exponential tower over the polynomial
    base, with `expTower c (r+1) = c^{expTower c r}` (the value sits one `expSeq`
    above the tower one shorter): the sequence side of `coord_layer_dominates`.
  * `dexp_exponent_floors` — the **positive companion to `dexp_not_const`**: the
    double exponential's *exponent* `cⁿ` (= the height-1 tower) floors under one
    ratio-lift, so the recursion that resolves `c^{cⁿ}` operates one axis down, on
    the exponent — exactly the new operation `DepthDoubleExp` showed `ratioN` lacks.

The `ω^ω` ceiling itself is not the end: diagonalising the tower *height* reaches
`ε₀`, and naming that act reproduces the residue (`DepthCeilingResidue`).  This file
pins the finite levels `ω^r` ∅-axiom; the `ω^ω`/`ε₀` reading is their classical
ordinal interpretation.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthOmegaTower

open E213.Lib.Math.Cauchy.DivergenceLadder (isConst)
open E213.Lib.Math.Cauchy.DepthTower (ratioLift geom_ratio_const)
open E213.Lib.Math.Cauchy.DepthExponentRecursion (expSeq)

/-! ## §1 — the depth-`r` tower coordinate -/

/-- The **depth-`r` tower coordinate**: an `r`-fold nested lexicographic product,
    `Coord 0 = Unit` (the ordinal `0`), `Coord (r+1) = Nat × Coord r`.  Read as a
    base-`ω` polynomial, it ranges over the ordinals below `ω^r`.  `Coord 2 =
    Nat × Nat × Unit` is `DepthOrdinal`'s `(h, d)` ordinal `ω·h + d < ω²`. -/
@[reducible] def Coord : Nat → Type
  | 0 => Unit
  | r+1 => Nat × Coord r

/-- Lexicographic order on `Coord r`, most-significant coefficient first: at level
    `r+1`, compare leading coefficients, breaking ties by the lower tower.  Read as
    `ω^r·a₁ + ⋯ < ω^r·b₁ + ⋯`.  `Coord 0` is a single point — nothing is below it. -/
def coordLt : (r : Nat) → Coord r → Coord r → Prop
  | 0,   _, _ => False
  | r+1, p, q => p.1 < q.1 ∨ (p.1 = q.1 ∧ coordLt r p.2 q.2)

/-- The all-zero coordinate `(0, …, 0)` — the ordinal `0`, the algebraic floor. -/
def coordZero : (r : Nat) → Coord r
  | 0 => ()
  | r+1 => (0, coordZero r)

/-! ## §2 — strict linear order -/

/-- `coordLt` is irreflexive. -/
theorem coord_irrefl : ∀ (r : Nat) (p : Coord r), ¬ coordLt r p p
  | 0,   _, h => h
  | r+1, p, h => by
    rcases h with h1 | ⟨_, h2⟩
    · exact Nat.lt_irrefl _ h1
    · exact coord_irrefl r p.2 h2

/-- `coordLt` is transitive. -/
theorem coord_trans : ∀ (r : Nat) (a b c : Coord r),
    coordLt r a b → coordLt r b c → coordLt r a c
  | 0,   _, _, _, h, _ => h.elim
  | r+1, _, _, _, hab, hbc => by
    rcases hab with h1 | ⟨he1, h2⟩
    · rcases hbc with h3 | ⟨he3, _⟩
      · exact Or.inl (Nat.lt_trans h1 h3)
      · exact Or.inl (he3 ▸ h1)
    · rcases hbc with h3 | ⟨he3, h4⟩
      · exact Or.inl (he1 ▸ h3)
      · exact Or.inr ⟨he1.trans he3, coord_trans r _ _ _ h2 h4⟩

/-- `coordLt` is total (trichotomy) — a *linear* order. -/
theorem coord_total : ∀ (r : Nat) (p q : Coord r),
    coordLt r p q ∨ p = q ∨ coordLt r q p
  | 0,   _, _ => Or.inr (Or.inl rfl)
  | r+1, p, q => by
    obtain ⟨pa, pp⟩ := p
    obtain ⟨qa, qp⟩ := q
    rcases Nat.lt_trichotomy pa qa with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases coord_total r pp qp with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨h, h2⟩)
      · exact Or.inr (Or.inl (by cases h; cases h2; rfl))
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h2⟩))
    · exact Or.inr (Or.inr (Or.inl h))

/-! ## §3 — well-foundedness: the ordinal property at every level -/

/-- Accessibility lifts one tower level: `Nat`-accessibility of the leading
    coefficient and `Coord r`-accessibility of the tail give `Coord (r+1)`
    accessibility, by nested `Acc.rec` (the `DepthOrdinal.lex_acc_aux` pattern,
    generalised to an arbitrary well-founded tail). -/
theorem coord_acc_step (r : Nat) (wfr : WellFounded (coordLt r)) :
    ∀ (a : Nat), Acc Nat.lt a → ∀ (p : Coord r), Acc (coordLt r) p →
      Acc (coordLt (r+1)) (a, p) := by
  intro a ha
  induction ha with
  | intro a _ iha =>
    intro p hp
    induction hp with
    | intro p _ ihp =>
      constructor
      rintro ⟨qa, qp⟩ hq
      rcases hq with h1 | ⟨he, h2⟩
      · exact iha qa h1 qp (wfr.apply qp)
      · subst he
        exact ihp qp h2

/-- ★★★ **`coordLt r` is well-founded for every `r`** — the depth-`r` tower
    coordinate is a genuine ordinal rank below `ω^r`, and the whole family is the
    `ω^ω` ladder, level by level.  `r = 2` recovers `DepthOrdinal.lex_wf` (`ω²`). -/
theorem coord_wf : ∀ r, WellFounded (coordLt r)
  | 0 => ⟨fun u => ⟨u, fun _ h => h.elim⟩⟩
  | r+1 => ⟨fun p => by
      obtain ⟨a, q⟩ := p
      exact coord_acc_step r (coord_wf r) a (Nat.lt_wfRel.wf.apply a)
        q ((coord_wf r).apply q)⟩

/-- ★★★ **The tower resolution always terminates, at every height.**  No sequence of
    depth-`r` coordinates descends forever: a real of finite tower coordinate is
    resolved by finitely many lifts, however many exponential layers it carries.
    The constructive content of `coord_wf` — the recursion bottoms out. -/
theorem coord_no_infinite_descent (r : Nat) :
    ¬ ∃ f : Nat → Coord r, ∀ n, coordLt r (f (n+1)) (f n) := by
  intro ⟨f, hf⟩
  have key : ∀ a, Acc (coordLt r) a → ∀ g : Nat → Coord r, g 0 = a →
      (∀ n, coordLt r (g (n+1)) (g n)) → False := by
    intro a ha
    induction ha with
    | intro x _ ih =>
      intro g hg0 hgf
      exact ih (g 1) (hg0 ▸ hgf 0) (fun n => g (n+1)) rfl (fun n => hgf (n+1))
  exact key (f 0) ((coord_wf r).apply (f 0)) f rfl hf

/-! ## §4 — the floor and the `ω`-multiplication of each layer -/

/-- The all-zero coordinate is the floor: nothing is strictly below `0`. -/
theorem coord_floor_minimal : ∀ (r : Nat) (p : Coord r),
    ¬ coordLt r p (coordZero r)
  | 0,   _, h => h
  | r+1, p, h => by
    obtain ⟨pa, pp⟩ := p
    rcases h with h1 | ⟨_, h2⟩
    · exact Nat.not_lt_zero pa h1
    · exact coord_floor_minimal r pp h2

/-- ★★★ **Each tower layer multiplies the rank by `ω`.**  A strictly larger leading
    coefficient outranks the *entire* lower tower: `(a, p) < (a+1, q)` for all tails
    `p, q`.  Reading the leading coefficient as the number of exponential layers
    resolved, `ω^r·a + ‹any sub-`ω^r`› < ω^r·(a+1)` — one exponential layer
    outweighs unboundedly much lower structure.  The ordinal shadow of
    `DepthDoubleExp` ("each exponential layer is a genuinely new axis"). -/
theorem coord_layer_dominates (r a : Nat) (p q : Coord r) :
    coordLt (r+1) (a, p) (a+1, q) :=
  Or.inl (Nat.lt_succ_self a)

/-! ## §5 — the sequence side: the exponential tower and its recursion -/

/-- The **`r`-fold exponential tower** over the polynomial base `id`:
    `expTower c 0 = (n ↦ n)`, `expTower c (r+1) = (n ↦ c^{expTower c r n})`.
    `expTower c 1 = (n ↦ cⁿ)`, `expTower c 2 = (n ↦ c^{cⁿ})` (the double
    exponential), and so on up the tower. -/
def expTower (c : Nat) : Nat → (Nat → Nat)
  | 0   => fun n => n
  | r+1 => expSeq c (expTower c r)

/-- ★★ **The tower sits one `expSeq` above the tower one shorter.**  `expTower c
    (r+1) = c^{expTower c r}` — the value-height is `1 +` the exponent-height
    (`DepthExponentRecursion`), iterated.  So a depth-`r` tower's resolution recurses
    `r` times into the exponent, one axis (= one `ω`-multiplication,
    `coord_layer_dominates`) per layer, bottoming at the polynomial base. -/
theorem expTower_succ (c r : Nat) :
    expTower c (r+1) = expSeq c (expTower c r) := rfl

/-- ★★★ **Positive companion to `DepthDoubleExp.dexp_not_const`.**  The single-ratio
    axis cannot floor the double exponential `c^{cⁿ}` (= `expTower c 2`).  But its
    *exponent* `cⁿ` (= `expTower c 1`) **does** floor — under one ratio-lift
    (`geom_ratio_const`: `ratioLift (cⁿ) = c`, constant).  So the operation that
    resolves `c^{cⁿ}` is the recursion of `DepthExponentRecursion` applied to the
    exponent, one axis down — precisely the new operation `dexp_not_const` shows a
    longer run of `ratioLift` lacks. -/
theorem dexp_exponent_floors (c : Nat) (hc : 1 ≤ c) :
    isConst (ratioLift (expTower c 1)) :=
  geom_ratio_const c hc

end E213.Lib.Math.Cauchy.DepthOmegaTower
