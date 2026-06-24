import E213.Lib.Math.NumberTheory.MulDescentRec

/-!
# The multiplicative carrier is the structural factorization list

The genesis-seam frontier's deepest residue (`research-notes/frontiers/the_genesis_seam.md`):
the multiplicative descent uses `Ω` as a *measure* (`MulDescentRec`), but its *carrier*
looked Nat-bound — `factorize` is fuel-recursion on the magnitude, seemingly unlike the
additive monoid, which is generated structurally on `List Unit` append.

This file dissolves the asymmetry.  The carrier of `×` is the **factorization list**
`factorize n : List Nat` (a list of distinguishable prime atoms), and on it the
multiplicative structure is *structural*, exactly dual to `List Unit → (ℕ, +)`:

  * **`×` is list append** — `prodL (a ++ b) = prodL a * prodL b`
    (`BigOmega.prodL_append`).  `prodL : (List Nat, ++, []) → (ℕ, ·, 1)` is the
    evaluation monoid-hom; the multiplicative monoid is the image of the *free monoid on
    prime atoms* under `prodL`, the `×`-dual of `replicate : (ℕ,+) ≅ (List Unit, ++)`.
  * **`Ω` is list length** — `Omega n = (factorize n).length` (`BigOmega.Omega_def`),
    the structural count (the `×`-dual of `Raw.leaves`).
  * **the peel is the structural tail** — `factorize (n / minFac n) = (factorize n).tail`
    (`factorize_descent_is_tail`).  The multiplicative descent `n ↦ n / minFac n` is,
    under `factorize`, literally `List.tail`: a structural `List` step, `List.rec`-native.
  * **the carrier evaluates back** — `prodL (factorize n) = n` (`factorize_prod`).

So the multiplicative descent's recursion, read on the carrier, is **structural `List`
recursion** (`mulDescent_is_list_rec`) — the leaves peel, not `Nat.strongRecOn`.

**Honest resolution of the asymmetry.**  The one magnitude-recursive piece that remains
is `factorize` itself — the *encoding* `ℕ → carrier`.  But that is exactly parallel to
the additive side, where the encoding `replicate : ℕ → List Unit` is also structural
recursion *on the Nat*.  In *both* monoids the **carrier structure and descent are
structural** (list append / tail); only the Nat→carrier encoding is magnitude-built.
The "× borrows Nat where + doesn't" worry was an artifact of comparing `×`'s encoding to
`+`'s structure; compared like-for-like, the two are the same shape over (in)distinguishable
atoms.  ∅-axiom throughout.
-/

namespace E213.Lib.Math.NumberTheory.FactorizationCarrier

open E213.Lib.Math.NumberTheory.PrimeFactorization
  (minFac prodL prodL_cons factorize factorize_prod)
open E213.Lib.Math.NumberTheory.BigOmega (Omega Omega_def prodL_append factorize_cons)

/-- ★★★ **The multiplicative peel is the structural list tail.**  Under `factorize`, the
    descent `n ↦ n / minFac n` *is* `List.tail`: `factorize` sends the peel to dropping the
    head prime atom.  So the multiplicative descent's step is a structural `List` step, not
    a `Nat`-magnitude step.  (Immediate from `factorize_cons`.)  ∅-axiom. -/
theorem factorize_descent_is_tail {n : Nat} (hn : 2 ≤ n) :
    factorize (n / minFac n) = (factorize n).tail :=
  (congrArg List.tail (factorize_cons hn)).symm

/-- ★★★ **The multiplicative descent is structural `List` recursion on the carrier.**  Any
    property `Q` of factorization lists transfers to `factorize n` by plain `List.rec`
    (structural — the leaves peel), with no `Nat.strongRecOn` / `Ω`-induction: the carrier
    is the structural list, the magnitude `n` only its `prodL`-evaluation. -/
theorem mulDescent_is_list_rec (Q : List Nat → Prop)
    (base : Q []) (cons : ∀ p ps, Q ps → Q (p :: ps)) :
    ∀ n, 1 ≤ n → Q (factorize n) := by
  intro n _
  generalize factorize n = L
  induction L with
  | nil => exact base
  | cons p ps ih => exact cons p ps ih

/-- ★★★ **The multiplicative carrier, structurally.**  Bundles the carrier picture: `×` is
    list append with `prodL` the evaluation hom (`prodL [] = 1`, `prodL (a++b) = prodL a *
    prodL b`); the carrier evaluates back (`prodL (factorize n) = n`); `Ω` is list length;
    the peel `n/minFac n` is the structural tail.  The multiplicative monoid `(ℕ≥1, ·)` is
    the `prodL`-image of the free monoid on prime atoms — the distinguishable-atom dual of
    `(ℕ, +) ≅ (List Unit, ++)`. -/
theorem mul_carrier_structural :
    (∀ a b : List Nat, prodL (a ++ b) = prodL a * prodL b)
    ∧ prodL ([] : List Nat) = 1
    ∧ (∀ n : Nat, 0 < n → prodL (factorize n) = n)
    ∧ (∀ n : Nat, Omega n = (factorize n).length)
    ∧ (∀ n : Nat, 2 ≤ n → factorize (n / minFac n) = (factorize n).tail) :=
  ⟨prodL_append, rfl, fun n hn => factorize_prod n hn, Omega_def,
   fun _ hn => factorize_descent_is_tail hn⟩

end E213.Lib.Math.NumberTheory.FactorizationCarrier
