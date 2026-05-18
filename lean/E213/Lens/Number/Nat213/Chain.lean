import E213.Lens.Number.Nat213.Raw

/-!
# Lens.Number.Nat213.Chain — Raw-subtype carrier for Method A chains

Option B of the lens-emergence roadmap (`research-notes/
2026-05-18_lens_emergence_path.md` §5).  Whereas `Core.lean` exposes
ℕ₊ as a *Nat*-subtype `{ n : Nat // 1 ≤ n }`, this file exposes the
dual *Raw*-subtype `{ r : Raw // IsMethodAChain r }` — a closed-Raw
arithmetic carrier with no external `Nat` appearing in the carrier
type itself.

The predicate `IsMethodAChain` is "this Raw equals `Raw.numeral n`
for some `n : Nat`".  Constructive: every chain element carries an
explicit witness.  ∅-axiom standard; no Mathlib / Classical /
propext / Quot.sound used.

Relation to the other files in this directory:
  - `Raw.lean`    — defines `numeral, succ, add, mul` (operations
                    that live on `Raw`, but the chain itself is not
                    a type).
  - `Core.lean`   — Nat-subtype ℕ₊ (`{ n : Nat // 1 ≤ n }`).
  - `Peano.lean`  — a separate inductive `Nat213`, parallel
                    definition.
  - `Bridge.lean` — Raw chain ↔ inductive Peano isomorphism.
  - `Chain.lean`  — *this file*: Raw-subtype ℕ₊.

`Chain.toNat : Chain → Nat` factors through `Raw.value`, so the
bridge to `Core.Nat213` (Nat-subtype) is one composition away.

**Framing**: this is the smallest "safe addition" step from the
research note.  Existing `Raw.lean` arithmetic is **not** modified
or deprecated; this file is purely additive.  See research note §7
Step 2.
-/

namespace E213.Lens.Number.Nat213

open E213.Theory

/-- A Raw `r` is a Method A chain element iff it equals
    `Raw.numeral n` for some `n : Nat`.  The existential carries
    the witness, so the predicate is constructive. -/
def IsMethodAChain (r : Raw) : Prop :=
  ∃ n : Nat, r = Raw.numeral n

theorem IsMethodAChain.one : IsMethodAChain Raw.one := ⟨0, rfl⟩

theorem IsMethodAChain.step {r : Raw} (h : IsMethodAChain r) :
    IsMethodAChain (Raw.succ r) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [hn]; rfl⟩

/-- Raw-subtype carrier for Method A chain elements. -/
structure Chain where
  val      : Raw
  property : IsMethodAChain val

namespace Chain

/-- Build a chain element from a Lean `Nat`; `numeral n` represents
    the `(n+1)`-th positive natural per the off-by-one convention.
    (Named `numeral` to avoid clashing with the structure's
    auto-generated `Chain.mk`.) -/
def numeral (n : Nat) : Chain := ⟨Raw.numeral n, ⟨n, rfl⟩⟩

/-- The chain element `1` (= `Raw.a`). -/
def one : Chain := numeral 0

theorem val_one : Chain.one.val = Raw.one := rfl

/-- Successor — closed within `Chain`. -/
def succ (c : Chain) : Chain :=
  ⟨Raw.succ c.val, IsMethodAChain.step c.property⟩

theorem val_succ (c : Chain) : (succ c).val = Raw.succ c.val := rfl

/-- Recover the Lean `Nat` (= leaves count). -/
def toNat (c : Chain) : Nat := Raw.value c.val

theorem toNat_numeral (n : Nat) : (numeral n).toNat = n + 1 :=
  Raw.value_numeral n

theorem toNat_one : Chain.one.toNat = 1 := rfl

theorem toNat_succ (c : Chain) : c.succ.toNat = c.toNat + 1 := by
  obtain ⟨n, hn⟩ := c.property
  show Raw.value (Raw.succ c.val) = Raw.value c.val + 1
  rw [hn]
  exact Raw.value_succ_of_ne _ (Raw.numeral_ne_b n)

end Chain

end E213.Lens.Number.Nat213
