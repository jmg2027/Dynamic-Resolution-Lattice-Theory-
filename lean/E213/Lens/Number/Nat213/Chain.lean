import E213.Lens.Number.Nat213.Raw

/-!
# Lens.Number.Nat213.Chain — Raw-subtype carrier with Nat-routed arithmetic

The Raw-subtype carrier `{ r : Raw // IsMethodAChain r }` for ℕ₊'s
Method A chart.  Operations route through `Nat` arithmetic and use
`Raw.numeral` to come back to a chain element: this realises Option
C of the lens-emergence path
.  The
"closed-Raw arithmetic" framing of the earlier Option B iteration
has been deliberately dropped — arithmetic on `Raw` is a category
error (Raw is for *representing* numbers, `Nat` is for *being*
them).

Relation to the other files in this directory:
  - `Raw.lean`    — canonical chart representative on `Raw`
                    (`one`, `succ`, `numeral`, `value`).
                    No `add` / `mul` — those live on `Nat`.
  - `Core.lean`   — `{n : Nat // 1 ≤ n}` Nat-subtype carrier
                    (alternative ℕ₊ carrier on the Nat side).
  - `Peano.lean`  — inductive `Nat213` with its own arithmetic.
  - `Bridge.lean` — Peano ↔ Raw chart bijection at the value level.

The natural bijection is `Chain ↔ Nat` via
`Chain.numeral / Chain.toNat`.  Operations on `Chain` are defined
by:
  - mapping to `Nat` via `toNat`
  - performing the `Nat` operation
  - mapping back via `numeral` (off-by-one adjusted)

∅-axiom standard; no Mathlib / Classical / propext / Quot.sound /
omega / native_decide.
-/

namespace E213.Lens.Number.Nat213

open E213.Theory

/-- A Raw `r` is a Method A chain element iff it equals
    `Raw.numeral n` for some `n : Nat`.  Existential predicate
    — constructive (witness exposed). -/
def IsMethodAChain (r : Raw) : Prop :=
  ∃ n : Nat, r = Raw.numeral n

theorem IsMethodAChain.one : IsMethodAChain Raw.one := ⟨0, rfl⟩

theorem IsMethodAChain.numeral (n : Nat) : IsMethodAChain (Raw.numeral n) :=
  ⟨n, rfl⟩

theorem IsMethodAChain.step {r : Raw} (h : IsMethodAChain r) :
    IsMethodAChain (Raw.succ r) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [hn]; rfl⟩

/-- Raw-subtype carrier for Method A chain elements. -/
structure Chain where
  val      : Raw
  property : IsMethodAChain val

namespace Chain

/-- Build a chain element from a Lean `Nat`.  `numeral n` represents
    the `(n+1)`-th positive natural (off-by-one convention).
    Named `numeral` to avoid clashing with the structure's
    auto-generated `Chain.mk`. -/
def numeral (n : Nat) : Chain := ⟨Raw.numeral n, ⟨n, rfl⟩⟩

/-- The chain element `1` (= `Raw.a`). -/
def one : Chain := numeral 0

theorem val_one : Chain.one.val = Raw.one := rfl

/-- Project a chain element to the underlying `Nat` (= leaves count). -/
def toNat (c : Chain) : Nat := Raw.value c.val

theorem toNat_numeral (n : Nat) : (numeral n).toNat = n + 1 :=
  Raw.value_numeral n

theorem toNat_one : Chain.one.toNat = 1 := rfl

/-- Every chain element has `toNat ≥ 1` — atoms have value 1, slash
    nodes only increase. -/
theorem toNat_ge_one (c : Chain) : 1 ≤ c.toNat := by
  obtain ⟨n, hn⟩ := c.property
  show 1 ≤ Raw.value c.val
  rw [hn, Raw.value_numeral n]
  exact Nat.succ_le_succ (Nat.zero_le n)

/-! ### Operations — defined via `Nat` arithmetic + `numeral` back-map

The carrier `Chain ↔ Nat` is bijective.  Operations on `Chain` are
defined by routing through `Nat` (where the abstract operations
live).  The off-by-one comes from `(numeral k).toNat = k + 1`. -/

/-- Successor on `Chain` — routes through `Nat.succ`. -/
def succ (c : Chain) : Chain := numeral c.toNat

/-- Closed addition on `Chain` — routes through `Nat.+`.  The
    `-1` adjusts for `numeral`'s off-by-one. -/
def add (c d : Chain) : Chain := numeral (c.toNat + d.toNat - 1)

/-- Closed multiplication on `Chain` — routes through `Nat.*`. -/
def mul (c d : Chain) : Chain := numeral (c.toNat * d.toNat - 1)

/-! ### `toNat` homomorphism

The Nat-routed definitions make `toNat` an obvious `+` / `*`
homomorphism.  The proofs use only `Nat.sub_add_cancel`
(Lean 4 core) plus `toNat_ge_one`. -/

theorem toNat_succ (c : Chain) : c.succ.toNat = c.toNat + 1 :=
  Raw.value_numeral c.toNat

theorem toNat_add (c d : Chain) : (c.add d).toNat = c.toNat + d.toNat := by
  show Raw.value (Raw.numeral (c.toNat + d.toNat - 1)) = c.toNat + d.toNat
  rw [Raw.value_numeral]
  exact Nat.succ_pred_eq_of_pos
    (Nat.le_trans (toNat_ge_one c) (Nat.le_add_right _ _))

theorem toNat_mul (c d : Chain) : (c.mul d).toNat = c.toNat * d.toNat := by
  show Raw.value (Raw.numeral (c.toNat * d.toNat - 1)) = c.toNat * d.toNat
  rw [Raw.value_numeral]
  have h : 0 < c.toNat * d.toNat := by
    have : 1 * 1 ≤ c.toNat * d.toNat :=
      Nat.mul_le_mul (toNat_ge_one c) (toNat_ge_one d)
    rwa [Nat.one_mul] at this
  exact Nat.succ_pred_eq_of_pos h

end Chain

end E213.Lens.Number.Nat213
