import E213.Lib.Math.Linalg213.Laplace

/-!
# Linalg213 — integer Cayley–Hamilton (toward the C-finite Hadamard product)

With the adjugate identity `M · adj M = det M · I` (`Laplace`) in hand, the matrix ring
infrastructure (`matMul` associativity, `matAdd`, the identity, powers) and the telescoping
that yields `χ_M(M) = 0`.

This file starts with the finite-sum **Fubini** (double-sum swap) that powers `matMul`
associativity.  All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.CayleyHamilton

open E213.Lib.Math.Linalg213.Permutation (sumZ iota)
open E213.Lib.Math.Linalg213.PermClosure (sumZ_map_add sumZ_map_smul map_eq_of_mem)
open E213.Lib.Math.Linalg213.Laplace (sumZ_append matMul)

/-! ## §1 — finite-sum Fubini -/

/-- The sum of a constant-`0` map is `0`. -/
theorem sumZ_map_zero {α : Type} : ∀ (L : List α), sumZ (L.map (fun _ => (0 : Int))) = 0
  | []     => rfl
  | _ :: l => by
    show (0 : Int) + sumZ (l.map (fun _ => (0 : Int))) = 0
    rw [sumZ_map_zero l, E213.Meta.Int213.zero_add]

/-- ★ **Fubini**: a double sum may be swapped. -/
theorem sumZ_swap {α β : Type} (g : α → β → Int) : ∀ (L1 : List α) (L2 : List β),
    sumZ (L1.map (fun j => sumZ (L2.map (fun k => g j k))))
      = sumZ (L2.map (fun k => sumZ (L1.map (fun j => g j k))))
  | [],      L2 => (sumZ_map_zero L2).symm
  | j :: js, L2 => by
    show sumZ (L2.map (fun k => g j k)) + sumZ (js.map (fun j => sumZ (L2.map (fun k => g j k))))
       = sumZ (L2.map (fun k => sumZ ((j :: js).map (fun j => g j k))))
    rw [sumZ_swap g js L2, ← sumZ_map_add]
    apply congrArg sumZ
    apply map_eq_of_mem
    intro k _
    rfl

/-- Right scalar pulls out of `sumZ`. -/
theorem sumZ_map_smul_right {α : Type} (c : Int) (f : α → Int) : ∀ (L : List α),
    sumZ (L.map f) * c = sumZ (L.map (fun x => f x * c))
  | []     => by show (0 : Int) * c = 0; rw [E213.Meta.Int213.zero_mul]
  | a :: l => by
    show (f a + sumZ (l.map f)) * c = f a * c + sumZ (l.map (fun x => f x * c))
    rw [E213.Meta.Int213.add_mul, sumZ_map_smul_right c f l]

/-! ## §2 — matrix multiplication is associative -/

/-- ★★ **`matMul` is associative** (pointwise). -/
theorem matMul_assoc (n : Nat) (M N P : Nat → Nat → Int) (i l : Nat) :
    matMul n M (matMul n N P) i l = matMul n (matMul n M N) P i l := by
  show sumZ ((iota n).map (fun j => M i j * matMul n N P j l))
     = sumZ ((iota n).map (fun k => matMul n M N i k * P k l))
  rw [map_eq_of_mem (fun j => M i j * matMul n N P j l)
        (fun j => sumZ ((iota n).map (fun k => M i j * (N j k * P k l))))
        (fun j _ => by
          show M i j * sumZ ((iota n).map (fun k => N j k * P k l))
             = sumZ ((iota n).map (fun k => M i j * (N j k * P k l)))
          rw [← sumZ_map_smul]),
      sumZ_swap (fun j k => M i j * (N j k * P k l)),
      map_eq_of_mem (fun k => sumZ ((iota n).map (fun j => M i j * (N j k * P k l))))
        (fun k => matMul n M N i k * P k l)
        (fun k _ => by
          show sumZ ((iota n).map (fun j => M i j * (N j k * P k l)))
             = sumZ ((iota n).map (fun j => M i j * N j k)) * P k l
          rw [sumZ_map_smul_right]
          apply congrArg sumZ
          apply map_eq_of_mem
          intro j _
          rw [E213.Meta.Int213.mul_assoc])]

end E213.Lib.Math.Linalg213.CayleyHamilton
