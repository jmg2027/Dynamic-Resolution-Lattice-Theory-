import E213.Lib.Math.Logic.ChildSelection

/-!
# Reverse Mathematics 213 — GA-cont: LPO ⟹ LLPO

Marathon field 17 (`blueprints/math/17_reverse_math_213.md`).

Completes the omniscience hierarchy's top edge.  Given an at-most-one-true stream, LPO
either finds the unique true index (its parity decides even/odd) or proves the stream
everywhere false (both halves vanish).  Parity is a native Bool `parity` recursion — no
`propext`.

Pure-Lean note (two obstacles resolved): (1) the Nat **literal** `+ 2` is stored as a GMP
literal, not `succ (succ 0)` — but `n + 2`, `n + 1 + 1`, and `Nat.succ (Nat.succ n)` are
all definitionally equal (`rfl`), so `parity` reductions go through.  (2) prefix `!` binds
*looser* than `=`, so `!(!b) = b` mis-parses as `!((!b) = b)` (a `decide`!); the fix is to
parenthesize the left `!`-expression: `(!(!b)) = b`.
-/

namespace E213.Lib.Math.Logic

/-- Native parity bit: `parity 0 = false`, flip each successor. -/
def parity : Nat → Bool
  | 0     => false
  | n + 1 => !(parity n)

theorem bnot_bnot : ∀ b : Bool, (!(!b)) = b
  | false => rfl
  | true  => rfl

/-- Even indices have parity `false`. -/
theorem parity_two_mul : ∀ k, parity (2 * k) = false
  | 0     => rfl
  | k + 1 => Eq.trans (bnot_bnot (parity (2 * k))) (parity_two_mul k)

/-- Odd indices have parity `true`. -/
theorem parity_two_mul_add_one (k : Nat) : parity (2 * k + 1) = true :=
  congrArg (fun b => !b) (parity_two_mul k)

/-- Every index is even or odd. -/
theorem even_or_odd : ∀ n : Nat, (∃ j, n = 2 * j) ∨ (∃ j, n = 2 * j + 1)
  | 0     => Or.inl ⟨0, rfl⟩
  | n + 1 => (even_or_odd n).elim
      (fun he => he.elim (fun j hj => Or.inr ⟨j, congrArg (fun m => m + 1) hj⟩))
      (fun ho => ho.elim (fun j hj => Or.inl ⟨j + 1, congrArg (fun m => m + 1) hj⟩))

/-- Even ≠ odd (via the parity bit). -/
theorem even_ne_odd (k j : Nat) (h : 2 * k = 2 * j + 1) : False :=
  Bool.noConfusion (Eq.trans (Eq.symm (parity_two_mul k))
    (Eq.trans (congrArg parity h) (parity_two_mul_add_one j)))

/-- Odd ≠ even. -/
theorem odd_ne_even (k j : Nat) (h : 2 * k + 1 = 2 * j) : False :=
  even_ne_odd j k (Eq.symm h)

/-- ★★ **LPO ⟹ LLPO**, ∅-axiom.  The unique true index (if any) lands at an even or odd
    position; the other parity is then entirely false (any true there would collide with
    it).  An everywhere-false stream makes both halves vanish. -/
theorem lpo_imp_llpo (hlpo : LPO) : LLPO :=
  fun f hone => (hlpo f).elim
    (fun he => he.elim (fun n0 hn0 =>
      (even_or_odd n0).elim
        (fun hev => hev.elim (fun j hj =>
          Or.inr (fun k => ne_true_imp_false (f (2 * k + 1)) (fun hodd =>
            odd_ne_even k j (Eq.trans (hone (2 * k + 1) n0 hodd hn0) hj)))))
        (fun hod => hod.elim (fun j hj =>
          Or.inl (fun k => ne_true_imp_false (f (2 * k)) (fun hev2 =>
            even_ne_odd k j (Eq.trans (hone (2 * k) n0 hev2 hn0) hj)))))))
    (fun hall => Or.inl (fun k => hall (2 * k)))

/-- ★★ **WLPO ⟹ LLPO**, ∅-axiom — the middle strut of the omniscience diagram,
    completing `LPO ⟹ WLPO ⟹ LLPO`.  Apply WLPO to the even substream
    `fun k => f (2*k)`.  If it is everywhere false, output the left half.  If WLPO
    returns its *negative* alternative `¬(∀ k, f(2*k)=false)`, the odd half is
    everywhere false — **without extracting any witness** (no Markov): were
    `f(2k+1)=true`, the at-most-one hypothesis would force every even index false
    (`even_ne_odd`), refuting the negative alternative by *constructing*
    `∀ j, f(2*j)=false`.  The parity verdict costs only firing-*decidability*, never
    the firing-*location* — the residue's even/odd readout is strictly cheaper than
    its witness readout. -/
theorem wlpo_imp_llpo (hwlpo : WLPO) : LLPO :=
  fun f hone =>
    (hwlpo (fun k => f (2 * k))).elim
      (fun hall => Or.inl hall)
      (fun hnot =>
        Or.inr (fun k =>
          ne_true_imp_false (f (2 * k + 1)) (fun hodd =>
            hnot (fun j =>
              ne_true_imp_false (f (2 * j)) (fun hev =>
                even_ne_odd j k (hone (2 * j) (2 * k + 1) hev hodd))))))

end E213.Lib.Math.Logic
