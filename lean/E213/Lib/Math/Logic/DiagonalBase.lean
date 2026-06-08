import E213.Lib.Math.Logic.Omniscience

/-!
# Reverse Mathematics 213 — Phase GC: the free interior (no-omniscience diagonal base)

Marathon field 17, Phase GC (`blueprints/math/17_reverse_math_213.md`).

The base of the ledger: the **diagonal / non-surjection** family costs **no omniscience** —
it is ∅-axiom outright (the `RCA₀`-analogue interior).  Here it is on the residue's own
Bool-stream carrier `Nat → Bool`: no enumeration of streams contains its own diagonal.
This is the same shape as `Lens/FlatOntologyClosure.object1_not_surjective` (the residue's
self-cover) and `Lib/Math/NumberSystems/Padic.zpSeq_not_enumerable` (the p-adic digit
tree) — one diagonal, no cost (`theory/essays/foundations/the_one_diagonal.md`).
-/

namespace E213.Lib.Math.Logic

/-- `!b ≠ b` (the one-bit flip differs), propext-free. -/
theorem bnot_ne (b : Bool) : (!b) = b → False := by
  cases b
  · exact fun h => Bool.noConfusion h
  · exact fun h => Bool.noConfusion h

/-- Cantor's diagonal of a stream enumeration: flip the `n`-th bit of the `n`-th stream. -/
def cantorDiag (e : Nat → Nat → Bool) : Nat → Bool := fun n => !(e n n)

/-- The diagonal differs from the `k`-th enumerated stream at index `k`. -/
theorem cantor_diag_differs (e : Nat → Nat → Bool) (k : Nat) : cantorDiag e k ≠ e k k :=
  bnot_ne (e k k)

/-- ★ **The Bool-stream carrier is not enumerable** (Cantor, no omniscience).  For any
    enumeration `e : ℕ → (ℕ → Bool)`, the diagonal differs from every `e k` — the
    cost-0 base of the reverse-math ledger. -/
theorem cantor_stream_not_enumerable (e : Nat → Nat → Bool) :
    ∃ d : Nat → Bool, ∀ k, ∃ n, d n ≠ e k n :=
  ⟨cantorDiag e, fun k => ⟨k, cantor_diag_differs e k⟩⟩

end E213.Lib.Math.Logic
