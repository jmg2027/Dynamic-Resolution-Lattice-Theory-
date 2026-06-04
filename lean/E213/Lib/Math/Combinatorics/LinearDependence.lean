import E213.Lib.Math.Combinatorics.BoolEnum

/-!
# The dimension bound is COUNT — `n+1` vectors in `𝔽₂^n` are dependent (∅-axiom)

Compiling the **linear-algebra / dimension method** (the engine behind Borsuk's
disproof, Frankl–Wilson, the cap-set bound) down the proof-ISA
(`seed/PROOF_ISA.md`).  Its primitive is "more than `n` vectors in an
`n`-dimensional space are linearly **dependent**" — apparently a *new* move, not
among the eight instructions.

Observation (the "why"): over `𝔽₂` it is **COUNT in a linear codomain**.  The
`2^m` subset-sums of `m` vectors live in `𝔽₂^n`, a space of `2^n` values; if
`m > n` then `2^m > 2^n`, so two distinct sub-selections **collide** (the
pigeonhole = COUNT, `nodup_length_le_of_subset`) — and a dependency is exactly
the residue of that sum-collision.  So the dimension method is not a new
instruction: it is the COUNT/`GAP` sub-mode read through the subset-sum Lens.
The dependency *is* a deficit in the value-space.

This file builds the collision (the COUNT step, ∅-axiom).  Turning a collision
into an *explicit* nontrivial `0`-combination is the completing rung
(`vsum`-linearity over selection-XOR + symmetric difference) — no new "why",
the same multiplicativity/COUNT already exhibited.

Companion "why": `theory/essays/proof_isa/linear_algebra_method.md`.
-/

namespace E213.Lib.Math.Combinatorics.LinearDependence

open E213.Lib.Math.Combinatorics.BoolEnum
open E213.Tactic.List213 (exists_of_mem_map length_map nodup_length_le_of_subset)

/-- The length-`n` zero vector. -/
def zeroVec : Nat → List Bool
  | 0 => []
  | n + 1 => false :: zeroVec n

theorem zeroVec_len : ∀ n, (zeroVec n).length = n
  | 0 => rfl
  | n + 1 => by show (zeroVec n).length + 1 = n + 1; rw [zeroVec_len n]

/-- `𝔽₂`-vector addition: pointwise XOR. -/
def vxor (a b : List Bool) : List Bool := List.zipWith xor a b

/-- XOR of equal-length vectors preserves length (∅-axiom, core `List.length_zipWith`
    would import `propext`). -/
theorem vxor_len_eq : ∀ (a b : List Bool), a.length = b.length → (vxor a b).length = a.length
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
      have hab : a.length = b.length := Nat.succ.inj h
      show (vxor a b).length + 1 = a.length + 1
      rw [vxor_len_eq a b hab]
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h

/-- Subset-sum: XOR the vectors of `vs` selected by `sel` (over `𝔽₂^n`). -/
def vsum (n : Nat) : List (List Bool) → List Bool → List Bool
  | [], _ => zeroVec n
  | v :: vs, true :: sel => vxor v (vsum n vs sel)
  | _ :: vs, false :: sel => vsum n vs sel
  | _ :: _, [] => zeroVec n

/-- Every subset-sum is a length-`n` vector (when all of `vs` are). -/
theorem vsum_len (n : Nat) :
    ∀ (vs : List (List Bool)) (sel : List Bool),
      (∀ v, v ∈ vs → v.length = n) → (vsum n vs sel).length = n
  | [], _, _ => zeroVec_len n
  | v :: vs, true :: sel, h => by
      show (vxor v (vsum n vs sel)).length = n
      have hv : v.length = n := h v (List.Mem.head _)
      have hvs : (vsum n vs sel).length = n :=
        vsum_len n vs sel (fun w hw => h w (List.Mem.tail _ hw))
      rw [vxor_len_eq v (vsum n vs sel) (by rw [hv, hvs]), hv]
  | _ :: vs, false :: sel, h => by
      show (vsum n vs sel).length = n
      exact vsum_len n vs sel (fun w hw => h w (List.Mem.tail _ hw))
  | _ :: _, [], _ => zeroVec_len n

/-- ★ **The dimension bound, as COUNT.**  If `vs` has more than `n` vectors,
    each of length `n`, then the subset-sum map collides on `allBoolLists` —
    i.e. its image is *not* `Nodup` — so two distinct sub-selections share a
    sum: a linear dependency exists.  Proof = `2^{|vs|} > 2^n` into a `2^n`-value
    space ⟹ pigeonhole (`nodup_length_le_of_subset`).  The dependency is the
    residue of the sum-collision; the dimension method is COUNT. -/
theorem dimension_bound_is_count (n : Nat) (vs : List (List Bool))
    (hlen : ∀ v, v ∈ vs → v.length = n) (hgt : n < vs.length) :
    ¬ ((allBoolLists vs.length).map (vsum n vs)).Nodup := by
  intro hnd
  have hsub : ∀ x, x ∈ (allBoolLists vs.length).map (vsum n vs) → x ∈ allBoolLists n := by
    intro x hx
    rcases exists_of_mem_map hx with ⟨sel, _, rfl⟩
    have hxn : (vsum n vs sel).length = n := vsum_len n vs sel hlen
    have hm := mem_allBoolLists (vsum n vs sel)
    rw [hxn] at hm
    exact hm
  have hle := nodup_length_le_of_subset hnd hsub
  rw [length_map, allBoolLists_length, allBoolLists_length] at hle
  have hchain : 2 ^ n < 2 ^ vs.length :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_succ (by decide)) (Nat.pow_le_pow_right (by decide) hgt)
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hchain hle)

end E213.Lib.Math.Combinatorics.LinearDependence
