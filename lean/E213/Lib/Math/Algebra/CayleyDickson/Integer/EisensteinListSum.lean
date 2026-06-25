import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaAlgebra213
import E213.Lib.Math.Combinatorics.Permutations

/-!
# Generic `ℤ[ω]`-valued list sums — the substrate for the Jacobi double sum (∅-axiom, Phase A3)

`listSum f L = Σ_{t ∈ L} f t` for any `f : ℕ → ℤ[ω]` — the list-indexed sum (the substrate the
permutation arguments need, where `EisensteinFiniteSum.sumRange` is index-by-`[0,n)`).  This generalises
`EisensteinCharSumZero.chiListSum` (`= listSum (chiOmega …)`), and provides the linearity + permutation
+ reindexing toolkit the **Jacobi-sum norm law `N(J) = p`** double sum is built from:

  * `listSum_lperm`     — permutation-invariance (`LPerm`)
  * `listSum_append`    — `Σ_{L₁ ++ L₂} = Σ_{L₁} + Σ_{L₂}`
  * `listSum_add` / `listSum_mul_left` / `listSum_congr` — linearity
  * `listSum_map`       — reindexing `Σ_{g·L} f = Σ_L (f ∘ g)`
  * `listSum_mul_distrib` — `(Σ_L f)·(Σ_M g) = Σ_{s∈L} Σ_{t∈M} f s · g t` (the double sum)

All clean ring inductions, ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Combinatorics.Permutations (LPerm)
open E213.Meta.Algebra213.Ring213
  (add_assoc add_comm add_zero zero_add add_left_comm add_4_swap_mid mul_add mul_zero)

/-- `Σ_{t ∈ L} f t` — the `ℤ[ω]`-valued sum over a list. -/
def listSum (f : Nat → ZOmega) : List Nat → ZOmega
  | [] => 0
  | t :: l => f t + listSum f l

@[simp] theorem listSum_nil (f : Nat → ZOmega) : listSum f [] = 0 := rfl
theorem listSum_cons (f : Nat → ZOmega) (t : Nat) (l : List Nat) :
    listSum f (t :: l) = f t + listSum f l := rfl

/-- ★★★ **Permutation invariance** — `LPerm l₁ l₂ ⟹ Σ_{l₁} f = Σ_{l₂} f`.  Induction on the
    permutation; `swap` is `add_left_comm`. -/
theorem listSum_lperm (f : Nat → ZOmega) {l₁ l₂ : List Nat} (h : LPerm l₁ l₂) :
    listSum f l₁ = listSum f l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih => show f a + listSum f _ = f a + listSum f _; rw [ih]
  | swap a b l =>
      show f b + (f a + listSum f l) = f a + (f b + listSum f l)
      rw [add_left_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- **`Σ_{L₁ ++ L₂} f = Σ_{L₁} f + Σ_{L₂} f`.** -/
theorem listSum_append (f : Nat → ZOmega) : ∀ (l₁ l₂ : List Nat),
    listSum f (l₁ ++ l₂) = listSum f l₁ + listSum f l₂
  | [], l₂ => by show listSum f l₂ = 0 + listSum f l₂; rw [zero_add]
  | t :: l₁, l₂ => by
      show f t + listSum f (l₁ ++ l₂) = f t + listSum f l₁ + listSum f l₂
      rw [listSum_append f l₁ l₂, add_assoc]

/-- **Additivity** — `Σ (f + g) = Σ f + Σ g`. -/
theorem listSum_add (f g : Nat → ZOmega) : ∀ (L : List Nat),
    listSum (fun t => f t + g t) L = listSum f L + listSum g L
  | [] => by show (0 : ZOmega) = 0 + 0; rw [add_zero]
  | t :: l => by
      show (f t + g t) + listSum (fun t => f t + g t) l = (f t + listSum f l) + (g t + listSum g l)
      rw [listSum_add f g l, add_4_swap_mid]

/-- **Left scalar factor** — `Σ (c · f) = c · Σ f`. -/
theorem listSum_mul_left (c : ZOmega) (f : Nat → ZOmega) : ∀ (L : List Nat),
    listSum (fun t => c * f t) L = c * listSum f L
  | [] => by show (0 : ZOmega) = c * 0; rw [mul_zero]
  | t :: l => by
      show c * f t + listSum (fun t => c * f t) l = c * (f t + listSum f l)
      rw [listSum_mul_left c f l, mul_add]

/-- **Congruence** — functions agreeing on `L` have equal sums. -/
theorem listSum_congr {f g : Nat → ZOmega} : ∀ (L : List Nat), (∀ t, t ∈ L → f t = g t) →
    listSum f L = listSum g L
  | [], _ => rfl
  | t :: l, h => by
      show f t + listSum f l = g t + listSum g l
      rw [h t (List.Mem.head l), listSum_congr l (fun s hs => h s (List.Mem.tail t hs))]

/-- **Reindexing** — `Σ_{g·L} f = Σ_L (f ∘ g)`. -/
theorem listSum_map (f : Nat → ZOmega) (g : Nat → Nat) : ∀ (L : List Nat),
    listSum f (L.map g) = listSum (fun t => f (g t)) L
  | [] => rfl
  | t :: l => by
      show f (g t) + listSum f (l.map g) = f (g t) + listSum (fun t => f (g t)) l
      rw [listSum_map f g l]

/-- ★★★★ **Product of sums is the double sum** — `(Σ_{s∈L} f s)·(Σ_{t∈M} g t) = Σ_{s∈L} Σ_{t∈M}
    f s · g t`.  Distributes the left sum termwise (`listSum_mul_left` on the inner sum), then sums over
    `L`.  The engine of the Jacobi-sum norm `N(J) = J·J̄ = p`. -/
theorem listSum_mul_distrib (f g : Nat → ZOmega) : ∀ (L M : List Nat),
    listSum f L * listSum g M = listSum (fun s => listSum (fun t => f s * g t) M) L
  | [], M => by show (0 : ZOmega) * listSum g M = 0; rw [E213.Meta.Algebra213.Ring213.zero_mul]
  | s :: l, M => by
      show (f s + listSum f l) * listSum g M
         = listSum (fun t => f s * g t) M + listSum (fun s => listSum (fun t => f s * g t) M) l
      rw [E213.Meta.Algebra213.Ring213.add_mul, listSum_mul_left (f s) g M,
          listSum_mul_distrib f g l M]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
