import E213.Theory.Raw
import E213.Prelude

/-!
# Infinity.Countable: Raw is at least ℕ-sized

**Σ3.**  An explicit injection `ℕ → Raw` via a right-leaning
tower of slashes.

The tower is built at the `Tree` level (where canonicality
can be discharged by one-step `cmp` facts), then wrapped into
`Raw` via the canonicality subtype.  Injectivity falls out of
leaf counts: `Raw.leaves (rawTower n) = n + 1`, so distinct
`n` yield distinct leaf counts, hence distinct Raw terms.

**Σ2** (Raw → ℕ injective) is *not* formalised here — it is a
standard countable-inductive-type fact not central to the
infinity-as-Lens thesis.  Σ3 alone establishes that Raw has
at least ℕ-many elements; combined with Cantor (Σ5) it
shows `Raw → Bool` is strictly larger than Raw.
-/

namespace E213.Lens.Cardinality

open E213.Theory.Internal (Tree)

/-- Right-leaning Tree tower: `treeTower 0 = b`,
    `treeTower (n+1) = a / (treeTower n)`.  Canonical at every
    level because `cmp a b = lt` and `cmp a (slash _ _) = lt`. -/
def treeTower : Nat → Tree
  | 0     => Tree.b
  | n + 1 => Tree.slash Tree.a (treeTower n)

theorem cmp_a_treeTower : ∀ n, Tree.cmp Tree.a (treeTower n) = .lt := by
  intro n; cases n with
  | zero => rfl
  | succ m => rfl

theorem treeTower_canonical :
    ∀ n, (treeTower n).canonical = true := by
  intro n; induction n with
  | zero => rfl
  | succ m ih =>
      show ((Tree.a.canonical && (treeTower m).canonical)
            && match Tree.cmp Tree.a (treeTower m)
                 with | .lt => true | _ => false) = true
      rw [cmp_a_treeTower, ih]
      rfl

theorem treeTower_leaves :
    ∀ n, (treeTower n).leaves = n + 1 := by
  intro n; induction n with
  | zero => rfl
  | succ m ih =>
      show Tree.a.leaves + (treeTower m).leaves = m + 1 + 1
      rw [ih]
      show 1 + (m + 1) = m + 1 + 1
      rw [Nat.add_comm 1 (m+1)]

end E213.Lens.Cardinality

namespace E213.Lens.Cardinality

open E213.Theory

/-- Lift the Tree tower to Raw by wrapping with canonicality. -/
def rawTower (n : Nat) : Raw := ⟨treeTower n, treeTower_canonical n⟩

/-- Leaves of the raw tower: `n + 1`. -/
theorem rawTower_leaves (n : Nat) : Raw.leaves (rawTower n) = n + 1 :=
  treeTower_leaves n

/-- **Σ3: ℕ injects into Raw.**  Different `n` yield `rawTower n`
    with different leaf counts, hence distinct Raw terms. -/
theorem rawTower_injective : Function.Injective rawTower := by
  intro m n heq
  have hleaf : Raw.leaves (rawTower m) = Raw.leaves (rawTower n) := by
    rw [heq]
  rw [rawTower_leaves, rawTower_leaves] at hleaf
  exact Nat.succ.inj hleaf

/-- Packaged: `∃ f : ℕ → Raw, Injective f`. -/
theorem raw_at_least_countable :
    ∃ f : Nat → Raw, Function.Injective f :=
  ⟨rawTower, rawTower_injective⟩

end E213.Lens.Cardinality
