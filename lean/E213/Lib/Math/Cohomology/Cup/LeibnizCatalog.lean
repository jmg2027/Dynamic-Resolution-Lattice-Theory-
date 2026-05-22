import E213.Lib.Math.Cohomology.Cup.LeibnizSym

/-!
# Cohomology.Cup.LeibnizCatalog — count-Lens recipe → δ-closure catalog

The Lens-recipe ↔ δ-closure correspondence:

> "For every count-Lens-canonical sorted single-partition recipe with
>  split position `s ∈ {0..k+l}`, the resulting cup operation
>  (admissible iff `s = k` or `s = l`) has a self-referential Leibniz
>  with the correction term at position `s` of the face list τ."

The catalog at single-partition recipes is **finite**: only `s = k`
(lex-projection) and `s = l` (mirror) give valid `Cochain k × Cochain l
→ Cochain (k+l)` signatures.

For ASYMMETRIC bidegrees (k ≠ l), the two recipes are distinct.  For
SYMMETRIC bidegrees (k = l), they coincide as functions but the
correction position differs (k vs l = k).  XOR symmetrisation
`cupSymList` gives a third recipe with doubled correction.

This file packages the catalog as a single theorem capturing the
recipe ↔ closure correspondence.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.LeibnizCatalog

open E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel
  (xorRange cupList deltaListR list_level_leibniz_general)
open E213.Lib.Math.Cohomology.Cup.LeibnizMirror (list_level_leibniz_mirror)
open E213.Lib.Math.Cohomology.Cup.LeibnizSym
  (cupSymList list_level_leibniz_sym)

/-! ## §1.  Sum-type for recipe choices -/

/-- Count-Lens-canonical sorted single-partition recipes admissible for
    bidegree `(k, l)`.  PURE. -/
inductive Recipe (k l : Nat) where
  | lex      -- s = k: α takes front-k, β takes back-l
  | mirror   -- s = l: β takes front-l, α takes back-k
  | sym      -- symmetric XOR of lex and mirror

/-- The split position associated to a recipe.  PURE. -/
def Recipe.splitPos {k l : Nat} : Recipe k l → Nat
  | .lex => k
  | .mirror => l
  | .sym => k  -- by convention; correction is XOR over both

/-! ## §2.  Cup-of-recipe at the list level -/

/-- Evaluate the cup product associated to a recipe at a list τ.
    PURE. -/
def cupOfRecipe {k l : Nat} (r : Recipe k l)
    (α β : List Nat → Bool) (τ : List Nat) : Bool :=
  match r with
  | .lex => cupList k l α β τ
  | .mirror => cupList l k β α τ
  | .sym => cupSymList k l α β τ

/-! ## §3.  Catalog capstone — recipe → Leibniz dispatch -/

/-- ★★★★★ **Catalog dispatch theorem** — for any recipe `r : Recipe k l`,
    `cupOfRecipe r` admits a twisted Leibniz at the list level whose
    correction sits at `r.splitPos` (`τ.eraseIdx r.splitPos`) for
    the lex/mirror branches, and is the XOR of both for the sym branch.

    The `sym` branch's RHS literally lists both sets of side terms
    and both corrections; the `lex` and `mirror` branches each reduce
    to G86 / `list_level_leibniz_mirror` directly.  PURE. -/
theorem catalog_dispatch (k l : Nat) (α β : List Nat → Bool)
    (τ : List Nat) (r : Recipe k l) :
    match r with
    | .lex =>
        xorRange (k + l + 1) (fun i => cupList k l α β (τ.eraseIdx i))
        = xor (xor (cupList (k+1) l (deltaListR k α) β τ)
                   (cupList k (l+1) α (deltaListR l β) τ))
              (cupList k l α β (τ.eraseIdx k))
    | .mirror =>
        xorRange (l + k + 1) (fun i => cupList l k β α (τ.eraseIdx i))
        = xor (xor (cupList (l+1) k (deltaListR l β) α τ)
                   (cupList l (k+1) β (deltaListR k α) τ))
              (cupList l k β α (τ.eraseIdx l))
    | .sym =>
        xorRange (k + l + 1) (fun i => cupSymList k l α β (τ.eraseIdx i))
        = xor (xor (xor (cupList (k+1) l (deltaListR k α) β τ)
                        (cupList k (l+1) α (deltaListR l β) τ))
                   (xor (cupList (l+1) k (deltaListR l β) α τ)
                        (cupList l (k+1) β (deltaListR k α) τ)))
              (xor (cupList k l α β (τ.eraseIdx k))
                   (cupList l k β α (τ.eraseIdx l))) := by
  cases r with
  | lex => exact list_level_leibniz_general k l α β τ
  | mirror => exact list_level_leibniz_mirror k l α β τ
  | sym => exact list_level_leibniz_sym k l α β τ

end E213.Lib.Math.Cohomology.Cup.LeibnizCatalog
