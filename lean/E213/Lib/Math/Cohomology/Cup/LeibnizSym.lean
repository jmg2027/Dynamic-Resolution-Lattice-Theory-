import E213.Lib.Math.Cohomology.Cup.LeibnizMirror

/-!
# Cohomology.Cup.LeibnizSym — symmetric cup + doubled-correction Leibniz

The **symmetric cup** `cupSym = α ⌣ β ⊕ β ⌣ α` (Bool XOR
symmetrisation).  Its δ-closure law has **two corrections**, one
at `τ[k]` (from α⌣β) and one at `τ[l]` (from β⌣α).  In ℤ/2 (Bool),
when `k = l` these collapse to a single XOR (both at the same
position).

Catalog row 6; see `theory/math/cohomology/cup.md`
self-reference section.

PURE — all theorems direct corollaries of
`LeibnizFinGeneral` + `list_level_leibniz_mirror`.
-/

namespace E213.Lib.Math.Cohomology.Cup.LeibnizSym

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Math.Cohomology.Cup.LeibnizMirror (cupRev)
open E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel
  (xorRange cupList deltaListR list_level_leibniz_general
   xorRange_congr)
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §1.  Symmetric cup definition (list level) -/

/-- ★ **Symmetric cup at the list level** — XOR symmetrisation of
    the lex-projection cup with its mirror.  When evaluated on a
    list τ of length k+l:

      cupSymList k l α β τ = cupList k l α β τ ⊕ cupList l k β α τ

    PURE definitional. -/
def cupSymList (k l : Nat) (α β : List Nat → Bool) (τ : List Nat) :
    Bool :=
  xor (cupList k l α β τ) (cupList l k β α τ)

/-! ## §2.  δ of symmetric cup at the list level -/

/-- Custom `xor` distributivity over xorRange (component-wise). -/
private theorem xorRange_xor_split (n : Nat) (f g : Nat → Bool) :
    xorRange n (fun i => xor (f i) (g i))
    = xor (xorRange n f) (xorRange n g) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    show xor (xorRange n' (fun i => xor (f i) (g i)))
              (xor (f n') (g n'))
       = xor (xor (xorRange n' f) (f n'))
              (xor (xorRange n' g) (g n'))
    rw [ih]
    cases xorRange n' f <;> cases xorRange n' g <;>
      cases f n' <;> cases g n' <;> rfl

/-- ★★★ **Symmetric Leibniz at the list level** — sum of the
    the list Leibniz at `(k, l)` and its mirror at `(l, k)`.  The
    correction is the XOR of the two boundary face values:

      `(α⌣β)(τ \ {τ[k]}) ⊕ (β⌣α)(τ \ {τ[l]})`

    which is `cupSymList`'s self-correction.  PURE. -/
theorem list_level_leibniz_sym
    (k l : Nat) (α β : List Nat → Bool) (τ : List Nat) :
    xorRange (k + l + 1) (fun i => cupSymList k l α β (τ.eraseIdx i))
    = xor (xor (xor (cupList (k+1) l (deltaListR k α) β τ)
                    (cupList k (l+1) α (deltaListR l β) τ))
               (xor (cupList (l+1) k (deltaListR l β) α τ)
                    (cupList l (k+1) β (deltaListR k α) τ)))
          (xor (cupList k l α β (τ.eraseIdx k))
               (cupList l k β α (τ.eraseIdx l))) := by
  -- LHS expands to sum of two xorRange'd cupList terms via xor distributivity
  have h_split : ∀ i,
      cupSymList k l α β (τ.eraseIdx i)
      = xor (cupList k l α β (τ.eraseIdx i))
            (cupList l k β α (τ.eraseIdx i)) := fun _ => rfl
  have h_cong : xorRange (k + l + 1)
                  (fun i => cupSymList k l α β (τ.eraseIdx i))
              = xorRange (k + l + 1)
                  (fun i => xor (cupList k l α β (τ.eraseIdx i))
                                (cupList l k β α (τ.eraseIdx i))) := by
    apply xorRange_congr
    intros; rfl
  rw [h_cong, xorRange_xor_split]
  -- Apply the list-level Leibniz to each factor
  rw [list_level_leibniz_general k l α β τ]
  -- For the second factor, use the mirror (k↔l swap).
  -- xorRange (k+l+1) of mirror cupList = xorRange (l+k+1) of mirror by Nat.add_comm
  have h_swap : k + l + 1 = l + k + 1 := by
    rw [Nat.add_comm k l]
  rw [show xorRange (k + l + 1)
            (fun i => cupList l k β α (τ.eraseIdx i))
         = xorRange (l + k + 1)
            (fun i => cupList l k β α (τ.eraseIdx i))
       from by rw [h_swap]]
  rw [list_level_leibniz_general l k β α τ]
  -- Pure XOR algebra to match
  cases cupList (k+1) l (deltaListR k α) β τ <;>
  cases cupList k (l+1) α (deltaListR l β) τ <;>
  cases cupList (l+1) k (deltaListR l β) α τ <;>
  cases cupList l (k+1) β (deltaListR k α) τ <;>
  cases cupList k l α β (τ.eraseIdx k) <;>
  cases cupList l k β α (τ.eraseIdx l) <;> rfl

end E213.Lib.Math.Cohomology.Cup.LeibnizSym
