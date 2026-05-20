import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Lens.Instances.Bool
import E213.Lens.Instances.Parity

/-!
# CompoundBoolLens: Bool × Bool-valued Lens, bootstrap-free

Note 25 §3 claim: there exist Lenses of backward-depth ≥ 2
that do **not** touch `Nat` bootstrap — they stay within
finite Bool-compounds.

This file realises the simplest such case: a `Bool × Bool`-
valued Lens whose two components are `parityLens` and
`boolXorLens`.

## §1. Compound Lens definition

The compound is the **pairwise fold** of parity and xor:
both components use `xor` as combine, but with different
base values (matching each inner Lens).
-/

namespace E213.Lens.Instances.CompoundBool

open E213.Theory E213.Lens
open E213.Lens.Instances.Bool E213.Lens.Instances.Parity

/-- Bool × Bool compound: first component tracks parity (like
    `parityLens`), second component tracks swap-visible xor
    (like `boolXorLens`).  Codomain = `Bool × Bool`, a 4-
    element finite type — **no Nat needed**. -/
def parityXorLens : Lens (Bool × Bool) where
  base_a  := (true, true)   -- parityLens base_a = T + boolXor base_a = T
  base_b  := (true, false)  -- parityLens base_b = T + boolXor base_b = F
  combine := fun p q => (xor p.1 q.1, xor p.2 q.2)

example : parityXorLens.view Raw.a = (true, true) := rfl
example : parityXorLens.view Raw.b = (true, false) := rfl

/-- First component of compound = parityLens. -/
theorem parityXor_fst_eq_parity (r : Raw) :
    (parityXorLens.view r).1 = parityLens.view r := by
  show (Raw.fold (true, true) (true, false)
         (fun p q => (xor p.1 q.1, xor p.2 q.2)) r).1
       = Raw.fold true true xor r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hsym_pair :
          ∀ (u v : Bool × Bool),
            (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) u v
          = (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) v u := by
        intro u v
        show (xor u.1 v.1, xor u.2 v.2) = (xor v.1 u.1, xor v.2 u.2)
        rw [Bool.xor_comm u.1 v.1, Bool.xor_comm u.2 v.2]
      have hsym_xor : ∀ u v : Bool, xor u v = xor v u :=
        fun u v => Bool.xor_comm u v
      rw [Raw.fold_slash _ _ _ hsym_pair x y h,
          Raw.fold_slash _ _ _ hsym_xor x y h]
      show xor (Raw.fold (true, true) (true, false)
                 (fun p q => (xor p.1 q.1, xor p.2 q.2)) x).1
               (Raw.fold (true, true) (true, false)
                 (fun p q => (xor p.1 q.1, xor p.2 q.2)) y).1
           = xor (Raw.fold true true xor x) (Raw.fold true true xor y)
      rw [ihx, ihy]


/-! ## §2. Second component = boolXorLens -/

theorem parityXor_snd_eq_boolXor (r : Raw) :
    (parityXorLens.view r).2 = boolXorLens.view r := by
  show (Raw.fold (true, true) (true, false)
         (fun p q => (xor p.1 q.1, xor p.2 q.2)) r).2
       = Raw.fold true false xor r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hsym_pair :
          ∀ (u v : Bool × Bool),
            (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) u v
          = (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) v u := by
        intro u v
        show (xor u.1 v.1, xor u.2 v.2) = (xor v.1 u.1, xor v.2 u.2)
        rw [Bool.xor_comm u.1 v.1, Bool.xor_comm u.2 v.2]
      have hsym_xor : ∀ u v : Bool, xor u v = xor v u :=
        fun u v => Bool.xor_comm u v
      rw [Raw.fold_slash _ _ _ hsym_pair x y h,
          Raw.fold_slash _ _ _ hsym_xor x y h]
      show xor (Raw.fold (true, true) (true, false)
                 (fun p q => (xor p.1 q.1, xor p.2 q.2)) x).2
               (Raw.fold (true, true) (true, false)
                 (fun p q => (xor p.1 q.1, xor p.2 q.2)) y).2
           = xor (Raw.fold true false xor x) (Raw.fold true false xor y)
      rw [ihx, ihy]

/-- **Compound factorisation.**  The Bool × Bool Lens IS the
    pairwise product of parityLens and boolXorLens. -/
theorem parityXor_is_pair (r : Raw) :
    parityXorLens.view r = (parityLens.view r, boolXorLens.view r) := by
  apply Prod.ext
  · exact parityXor_fst_eq_parity r
  · exact parityXor_snd_eq_boolXor r


/-! ## §3. Image has ≥ 3 elements — genuinely Bool × Bool valued

Raw term `a/b` gives a third image point, distinct from
view(a) = (true, true) and view(b) = (true, false).

(The fourth point (false, ·) appears at level ≥ 3; here we
just verify 3.  See note 25 §3 discussion of level-3 reach.)
-/

/-- `a/b` Raw term. -/
def ab : Raw := Raw.slash Raw.a Raw.b (by decide)

/-- view (a/b) = (false, true) — third distinct image point. -/
theorem parityXor_ab : parityXorLens.view ab = (false, true) := by
  show Raw.fold (true, true) (true, false)
         (fun p q => (xor p.1 q.1, xor p.2 q.2))
         (Raw.slash Raw.a Raw.b (by decide)) = (false, true)
  have hsym_pair :
      ∀ (u v : Bool × Bool),
        (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) u v
      = (fun p q : Bool × Bool => (xor p.1 q.1, xor p.2 q.2)) v u := by
    intro u v
    show (xor u.1 v.1, xor u.2 v.2) = (xor v.1 u.1, xor v.2 u.2)
    rw [Bool.xor_comm u.1 v.1, Bool.xor_comm u.2 v.2]
  rw [Raw.fold_slash _ _ _ hsym_pair Raw.a Raw.b (by decide)]
  rfl

/-- **Image cardinality ≥ 3**: three distinct Raw terms give
    three distinct Bool × Bool outputs. -/
theorem parityXor_image_ge_three :
    ∃ r₁ r₂ r₃ : Raw,
      parityXorLens.view r₁ ≠ parityXorLens.view r₂ ∧
      parityXorLens.view r₁ ≠ parityXorLens.view r₃ ∧
      parityXorLens.view r₂ ≠ parityXorLens.view r₃ := by
  refine ⟨Raw.a, Raw.b, ab, ?_, ?_, ?_⟩
  all_goals decide


/-! ## §4. Bootstrap-free claim (informal)

Codomain `Bool × Bool` is constructed from:
- `Bool`: Lean inductive with constructors `true`, `false`.
  No `Nat` used.
- `×`: product type constructor.  No `Nat` used.

Therefore the backward chain for `parityXorLens` is:
```
parityXorLens : Lens (Bool × Bool)
 ├─ Bool × Bool ← Bool + ×  (no Nat)
 ├─ (true, true), (true, false) ← Bool constants (no Nat)
 ├─ combine ← componentwise xor on Bool (no Nat)
```

depth: 2 (Lens → Bool × Bool → Bool → Raw).
bootstrap: **none**.

This is the simplest witness of note 25 §3's finite compound
tower claim.  Contrast with `Lens.leaves : Lens Nat` which has
depth 2 but **with** Nat bootstrap.

### Consequence

The backward depth of a Lens alone is not a full complexity
measure — we must also track **whether the chain encounters
bootstrap**.  Two Lenses with equal depth may be:
- Both bootstrap-free → purely finite-combinatorial.
- Both bootstrap → both encounter self-reference fixed point.
- Mixed → different classification.

`parityXorLens` (depth 2, bootstrap-free) vs `Lens.leaves`
(depth 2, bootstrap) demonstrate the distinction.

-/

end E213.Lens.Instances.CompoundBool
