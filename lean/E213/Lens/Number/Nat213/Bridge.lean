import E213.Lens.Number.Nat213.Raw
import E213.Lens.Number.Nat213.Peano

/-!
# Lens.Number.Nat213.Bridge — Peano ↔ Method A Raw chart bijection

Two equivalent ℕ₊ representations:
  - Raw chart (canonical Lens-derived):  `Lens.Number.Nat213.Raw`
      — Method A Raw chain: `one := Raw.a`, `succ n := slashOrSelf n
      Raw.b`.
  - Inductive Peano (ergonomic parallel):  `Lens.Number.Nat213.
      Peano.Nat213` — `inductive | one | succ`.

This module is the bridge between them at the **`value`** level:

  - `toRaw : Peano.Nat213 → Raw` — the chart embedding
  - `value_toRaw : Raw.value (toRaw n) = n.toNat` — projection bijection

Arithmetic homomorphism is expressed at the **value level**
(`Raw.value (toRaw (m + n)) = m.toNat + n.toNat`) rather than at
the Raw operation level: per
`research-notes/2026-05-18_lens_emergence_path.md` §5 Option C, the
abstract number-theoretic operations live on `Nat`, and the Raw
side carries only the chart representative.  Closed-Raw arithmetic
has been deliberately removed from `Raw.lean`; consumers that
previously used `Raw.add` / `Raw.mul` should now use Peano
arithmetic (via the `+` / `*` instances) followed by `toRaw` and
`value_toRaw_add` / `value_toRaw_mul`.

∅-axiom standard; no Mathlib / Classical / propext / Quot.sound /
omega / native_decide.
-/

namespace E213.Lens.Number.Nat213.Bridge

open E213.Theory
open E213.Term.Internal (Tree)

/-! ### Chart embedding: Peano.Nat213 → Raw -/

/-- `toRaw n` — embed the inductive `Nat213` element into the
    Method A Raw chain. -/
def toRaw : E213.Lens.Number.Nat213.Peano.Nat213 → Raw
  | .one    => E213.Lens.Number.Nat213.Raw.one
  | .succ k => E213.Lens.Number.Nat213.Raw.succ (toRaw k)

theorem toRaw_one :
    toRaw E213.Lens.Number.Nat213.Peano.Nat213.one
      = E213.Lens.Number.Nat213.Raw.one := rfl

theorem toRaw_succ (k : E213.Lens.Number.Nat213.Peano.Nat213) :
    toRaw (E213.Lens.Number.Nat213.Peano.Nat213.succ k)
      = E213.Lens.Number.Nat213.Raw.succ (toRaw k) := rfl

/-! ### Chain invariant on the image -/

/-- The image of `toRaw` never equals `Raw.b` — Method A chain
    invariant transported through the bijection. -/
theorem toRaw_ne_b (k : E213.Lens.Number.Nat213.Peano.Nat213) :
    toRaw k ≠ Raw.b := by
  induction k with
  | one =>
      intro h
      have hval : Raw.a.val = Raw.b.val := congrArg Subtype.val h
      exact Tree.noConfusion hval
  | succ k ih =>
      show E213.Lens.Number.Nat213.Raw.succ (toRaw k) ≠ Raw.b
      unfold E213.Lens.Number.Nat213.Raw.succ
             E213.Theory.Raw.Endomorphic.slashOrSelf
      rw [dif_neg ih]
      intro h
      have hval : (Raw.slash (toRaw k) Raw.b ih).val = Raw.b.val :=
        congrArg Subtype.val h
      unfold Raw.slash at hval
      split at hval
      · exact Tree.noConfusion hval
      · exact Tree.noConfusion hval
      · rename_i hcmp
        exact ih (Subtype.ext (Tree.cmp_eq_to_eq _ _ hcmp))

/-! ### Value bijection: `Raw.value (toRaw n) = n.toNat` -/

/-- Inductive Peano's `toNat` and the Raw chain's `value` agree
    along the chart embedding `toRaw`. -/
theorem value_toRaw (m : E213.Lens.Number.Nat213.Peano.Nat213) :
    E213.Lens.Number.Nat213.Raw.value (toRaw m) = m.toNat := by
  induction m with
  | one => rfl
  | succ k ih =>
      show E213.Lens.Number.Nat213.Raw.value
              (E213.Lens.Number.Nat213.Raw.succ (toRaw k))
         = k.toNat + 1
      rw [E213.Lens.Number.Nat213.Raw.value_succ_of_ne _ (toRaw_ne_b k), ih]

/-! ### Value-level arithmetic homomorphism

These express the additive / multiplicative homomorphism property
at the `Nat` level, going through Peano's `Nat213.add` / `mul`
(rather than a Raw-level `Raw.add` / `Raw.mul`, which no longer
exists per Option C).
-/

/-- `Raw.value (toRaw (m + n)) = m.toNat + n.toNat`. -/
theorem value_toRaw_add (m n : E213.Lens.Number.Nat213.Peano.Nat213) :
    E213.Lens.Number.Nat213.Raw.value
        (toRaw (E213.Lens.Number.Nat213.Peano.Nat213.add m n))
      = m.toNat + n.toNat := by
  rw [value_toRaw, E213.Lens.Number.Nat213.Peano.Nat213.toNat_add]

/-- `Raw.value (toRaw (m · n)) = m.toNat · n.toNat`. -/
theorem value_toRaw_mul (m n : E213.Lens.Number.Nat213.Peano.Nat213) :
    E213.Lens.Number.Nat213.Raw.value
        (toRaw (E213.Lens.Number.Nat213.Peano.Nat213.mul m n))
      = m.toNat * n.toNat := by
  rw [value_toRaw, E213.Lens.Number.Nat213.Peano.Nat213.toNat_mul]

/-! ### Bridge injectivity (, iteration #7)

`toRaw` is injective: distinct `Peano.Nat213` elements embed to
distinct Raws.  Combines `value_toRaw` (bijection at the Nat level)
with `Peano.Nat213.toNat_injective`. -/

/-- **Bridge injectivity**: `toRaw m = toRaw n → m = n`.  Follows
    from `value_toRaw` projecting both sides to `toNat`, then
    `Peano.toNat_injective` lifting back. -/
theorem toRaw_injective
    {m n : E213.Lens.Number.Nat213.Peano.Nat213} (h : toRaw m = toRaw n) :
    m = n := by
  have h1 : E213.Lens.Number.Nat213.Raw.value (toRaw m)
          = E213.Lens.Number.Nat213.Raw.value (toRaw n) := by rw [h]
  rw [value_toRaw, value_toRaw] at h1
  exact E213.Lens.Number.Nat213.Peano.Nat213.toNat_injective h1

end E213.Lens.Number.Nat213.Bridge
