import E213.Lib.Math.Analysis.Cauchy.DepthTower

/-!
# DepthOrdinal — the divergence coordinate is an ordinal below ω²

`DepthTower` gave every constructive real a two-axis coordinate `(h, d)`:
log-height `h` (how many ratio-lifts/logarithms to reach polynomial class) above
poly-depth `d` (finite differences to a constant).  This file shows that coordinate
*is* an ordinal: reading `(h, d)` as `ω·h + d`, the lexicographic order is a
**well-founded strict linear order** — an honest model of the ordinals below `ω²`.

Why this is the right closure of the whole arc.  The user's frame —"handle the
infinite by a finite reference; when that reference is itself infinite, climb one
axis; iterate" — produces exactly a descending walk in this order: a diff-lift
lowers `d`, and resolving a difference-axis ∞ by a ratio-lift lowers `h` (and
resets `d`).  Well-foundedness (`lex_wf`) is the theorem that **this walk always
terminates**: there is no infinitely-deferring real of finite coordinate
(`no_infinite_descent`).  The coordinate is a constructive-complexity *ordinal
rank*:

  | real / cross-det | coordinate `(h,d)` | ordinal `ω·h + d` |
  |---|---|---|
  | algebraic (φ, √2): const cross-det | `(0, 0)` | `0` |
  | `cⁿ` (exponent degree 1) | `(1, 0)` | `ω` |
  | `c^{n²}` (exponent degree 2) | `(2, 0)` | `ω·2` |

Here `h` is the *exponent's polynomial degree* (`ratioLift = diff-on-exponent`,
`DepthTower`), not an iterated-log height.  The reals with a finite `(h, d)` are
exactly those whose cross-determinant is `c^{polynomial}`.  e (cross-det `n!`), π,
Liouville `c^{k!}` and the iterated exponentials are **beyond** this finite-`(h,d)`
reach (super-polynomial exponents); resolving them needs a genuinely new operation —
a *ratio on the exponent* (the `(ratio,diff)` ladder applied to the exponent
sequence), a self-similar recursion that is the frontier toward `ε₀`, not captured
by finitely many `ratioLift`s.  This file proves the well-order for the finite
`(h,d)` reals.

This file proves the ordinal structure (`lexLt` is irreflexive, transitive, total,
well-founded) ∅-axiom; the coordinate assignment itself is
`DepthTower.atTowerCoord`.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.DepthOrdinal

/-- The **divergence-depth coordinate** `(h, d)` — log-height `h` above poly-depth
    `d`, read as the ordinal `ω·h + d`.  Below `ω²`. -/
abbrev DepthOrd : Type := Nat × Nat

/-- Lexicographic order on `DepthOrd`: `(h₁,d₁) < (h₂,d₂)` iff `h₁ < h₂`, or
    `h₁ = h₂` and `d₁ < d₂` — i.e. `ω·h₁ + d₁ < ω·h₂ + d₂`. -/
def lexLt (p q : DepthOrd) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-! ## §1 — strict linear order -/

/-- `lexLt` is irreflexive. -/
theorem lex_irrefl (p : DepthOrd) : ¬ lexLt p p := by
  intro h; rcases h with h1 | ⟨_, h2⟩
  · exact Nat.lt_irrefl _ h1
  · exact Nat.lt_irrefl _ h2

/-- `lexLt` is transitive. -/
theorem lex_trans (a b c : DepthOrd) (hab : lexLt a b) (hbc : lexLt b c) :
    lexLt a c := by
  rcases hab with h1 | ⟨he1, h2⟩
  · rcases hbc with h3 | ⟨he3, _⟩
    · exact Or.inl (Nat.lt_trans h1 h3)
    · exact Or.inl (he3 ▸ h1)
  · rcases hbc with h3 | ⟨he3, h4⟩
    · exact Or.inl (he1 ▸ h3)
    · exact Or.inr ⟨he1.trans he3, Nat.lt_trans h2 h4⟩

private theorem pair_eq (p q : DepthOrd) (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q := by
  cases p; cases q; cases h1; cases h2; rfl

/-- `lexLt` is total (trichotomy) — a *linear* order. -/
theorem lex_total (p q : DepthOrd) : lexLt p q ∨ p = q ∨ lexLt q p := by
  rcases Nat.lt_trichotomy p.1 q.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Nat.lt_trichotomy p.2 q.2 with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h, h2⟩)
    · exact Or.inr (Or.inl (pair_eq p q h h2))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h2⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-! ## §2 — well-foundedness: the ordinal property -/

/-- Accessibility from the `Nat`-accessibility of both coordinates, by nested
    `Acc.rec` (Lean-core `Nat.strong_induction_on` is unavailable here; `Nat.lt`
    well-foundedness is `Nat.lt_wfRel.wf`). -/
private theorem lex_acc_aux :
    ∀ h, Acc Nat.lt h → ∀ d, Acc Nat.lt d → Acc lexLt (h, d) := by
  intro h hh
  induction hh with
  | intro h _ ihh =>
    intro d hd
    induction hd with
    | intro d _ ihd =>
      constructor
      intro q hq
      rcases hq with h1 | ⟨he, h2⟩
      · have hqr : q = (q.1, q.2) := by cases q; rfl
        rw [hqr]; exact ihh q.1 h1 q.2 (Nat.lt_wfRel.wf.apply q.2)
      · have hq2 : q = (h, q.2) := by cases q; cases he; rfl
        rw [hq2]; exact ihd q.2 h2

/-- Every coordinate is accessible. -/
theorem lex_acc (h d : Nat) : Acc lexLt (h, d) :=
  lex_acc_aux h (Nat.lt_wfRel.wf.apply h) d (Nat.lt_wfRel.wf.apply d)

/-- ★★★ **`lexLt` is well-founded** — the defining property of an ordinal.  The
    divergence-depth coordinate is a genuine ordinal rank below `ω²`; there is no
    infinite descending chain of coordinates. -/
theorem lex_wf : WellFounded lexLt := ⟨fun p => by cases p; exact lex_acc _ _⟩

/-- ★★★ **The resolution always terminates.**  No sequence of coordinates descends
    forever under `lexLt`: a real of finite divergence coordinate is resolved by
    finitely many lifts.  This is the constructive content of well-foundedness —
    the "finite reference for the infinite, iterated" tower bottoms out. -/
theorem no_infinite_descent :
    ¬ ∃ f : Nat → DepthOrd, ∀ n, lexLt (f (n+1)) (f n) := by
  intro ⟨f, hf⟩
  have acc : Acc lexLt (f 0) := lex_wf.apply (f 0)
  -- descend along f using accessibility
  have key : ∀ a, Acc lexLt a → ∀ g : Nat → DepthOrd, g 0 = a →
      (∀ n, lexLt (g (n+1)) (g n)) → False := by
    intro a ha
    induction ha with
    | intro x _ ih =>
      intro g hg0 hgf
      exact ih (g 1) (hg0 ▸ hgf 0) (fun n => g (n+1)) rfl (fun n => hgf (n+1))
  exact key (f 0) acc f rfl hf

/-! ## §3 — the coordinate's floor and the algebraic base -/

/-- The ordinal floor `(0,0)` — rank `0`, the algebraic base (constant
    cross-determinant).  Nothing is strictly below it. -/
theorem floor_minimal (p : DepthOrd) : ¬ lexLt p (0, 0) := by
  intro h
  rcases h with h1 | ⟨_, h2⟩
  · exact Nat.not_lt_zero _ h1
  · exact Nat.not_lt_zero _ h2

/-- The log-axis dominates: any increase in log-height outranks every poly-depth —
    `(h, d) < (h+1, d')` for all `d, d'`.  `ω·h + d < ω·(h+1) + d'`: a single
    logarithm of growth outweighs unboundedly many differences. -/
theorem log_axis_dominates (h d d' : Nat) : lexLt (h, d) (h+1, d') :=
  Or.inl (Nat.lt_succ_self h)

end E213.Lib.Math.Analysis.Cauchy.DepthOrdinal
