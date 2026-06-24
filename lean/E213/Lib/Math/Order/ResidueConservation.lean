import E213.Lib.Math.Order.KnasterResidue

/-!
# The residue-conservation move catalogue (∅-axiom)

`theory/essays/foundations/the_conserved_residue.md`: a totality-claim handles the power-object gap
by a **move**, and every move *relocates* the residue, never destroys it.  Four moves; this file
completes the catalogue (`adjoin`/`restrict` are verified in `KnasterResidue`; `stratify`/`quotient`
are added here).

| move | what it does | where the residue goes | witness |
|---|---|---|---|
| **adjoin** | complete the lattice (add the limit) | the completeness datum / the adjoined `∞` | `KnasterResidue.knaster_conclusion_false_on_nat` (`succ`/ℕ) |
| **restrict** | narrow the map-class | out of the class's view (the fpf member is excluded) | `KnasterResidue.residue_is_class_dependent` (`Bool`, monotone) |
| **stratify** | ascend a level — cover α's residue at a bigger type | the **next rung**; the tower never closes | `nat_lt_two_pow` (`n < 2^n`) |
| **quotient** | identify the residue away | "does a computable normal form exist" — decidable ⟹ free, undecidable ⟹ residue | `parity_idempotent` (the mod-2 section) |

The unifying fact: the residue is `object1_not_surjective` = Cantor's gap, present at every level
(`OneDiagonal.cantor_via_lawvere {T}` for *every* `T`).  No move removes it; each pays for "closure"
by relocating it.  ∅-axiom throughout.
-/

namespace E213.Lib.Math.Order.ResidueConservation

/-! ## Stratify — the power-object strictly exceeds the carrier at every level

The cover of `α`'s residue lives one level up (`α → Bool` is strictly bigger than `α`).  The
cardinality engine is `n < 2^n`: every rung of the power-object tower is strictly taller, so the
ascent never reaches a residue-free top.  "Infinity is the residue's shape" (CLAUDE.md) is this
never-closing tower. -/

/-- `0 < 2^n` — every power-object level is inhabited. -/
theorem two_pow_pos : ∀ n : Nat, 0 < 2 ^ n
  | 0     => Nat.zero_lt_one
  | n + 1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_pos (two_pow_pos n) (Nat.succ_pos 1)

/-- ★★★ **Stratify conserves the residue.**  `n < 2^n`: the power-object `α → Bool` strictly exceeds
    its carrier at *every* level, so covering one level's residue forces a strictly larger level,
    which has its own — the ascent never terminates in a residue-free top.  The cardinality reason
    Cantor's diagonal cannot be dodged by ascending; the stratify move relocates the residue up one
    rung, never off the tower. -/
theorem nat_lt_two_pow : ∀ n : Nat, n < 2 ^ n
  | 0     => Nat.zero_lt_one
  | n + 1 => by
    have ih : n + 1 ≤ 2 ^ n := nat_lt_two_pow n
    have hp : 0 < 2 ^ n := two_pow_pos n
    have e : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_two]
    have h2 : 2 ^ n < 2 ^ n + 2 ^ n := Nat.lt_add_of_pos_left hp
    rw [e]
    exact Nat.lt_of_le_of_lt ih h2

/-! ## Quotient — a decidable equivalence has a total idempotent section (residue-free)

The quotient move identifies the residue away.  When the equivalence is **decidable** it has a
computable normal form — a total idempotent retraction — so the quotient is genuinely residue-free
(this is the free group's `proj`, here minimally as parity mod 2).  The residue is relocated into
*"does a computable normal form exist"*: a decidable equivalence has one (free); an **undecidable**
one does not, and the missing section *is* the residue.  That undecidable side is not exhibitable in
∅-axiom data — which is precisely the point (an un-computable normal form is a non-constructible
residue, `reached_by_none.md`). -/

/-- Normal form of the decidable "same parity" quotient of ℕ — the residue mod 2. -/
def parity (n : Nat) : Nat := n % 2

/-- ★★★ **Quotient (decidable side) conserves nothing — it is residue-free.**  `parity` is a total
    idempotent retraction (`parity ∘ parity = parity`): a computable normal form, so the parity
    quotient of ℕ has a total section and leaves no residue.  The minimal analogue of the free
    group's `freeReduce_idempotent`/`proj`; residue-freeness here *is* the decidability of `% 2`. -/
theorem parity_idempotent (n : Nat) : parity (parity n) = parity n :=
  Nat.mod_eq_of_lt (Nat.mod_lt n (Nat.succ_pos 1))

/-- The section lands in the finite normal-form set `{0, 1}` — the quotient collapses ℕ to a finite
    type, which (being finite, not reaching the power-object) is genuinely residue-free. -/
theorem parity_range : ∀ n : Nat, parity n = 0 ∨ parity n = 1 := by
  intro n
  have h : n % 2 < 2 := Nat.mod_lt n (Nat.succ_pos 1)
  show n % 2 = 0 ∨ n % 2 = 1
  match hk : n % 2, h with
  | 0,     _ => exact Or.inl rfl
  | 1,     _ => exact Or.inr rfl
  | k + 2, hk2 => exact absurd hk2 (Nat.not_lt_of_le (Nat.le_add_left 2 k))

end E213.Lib.Math.Order.ResidueConservation
