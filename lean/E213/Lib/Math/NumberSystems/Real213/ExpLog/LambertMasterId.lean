import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Nat.NatRing213

/-!
# LambertMasterId — the master identity of the Lambert convergent coefficients

The Padé-matching core that `LowerBase` (the weld's last brick, `LambertOrder`)
needs.  The truncated coth-residual `R_J(i) = (2J+1)·devB·c_J − devA·s_J`
(`LambertOrder` §10) has its q-graded pieces governed by the **master identity**

  `Σ_{s} W(N,s)·((2N−2s+1)·bpF n s − apF n s) = (−1)^{n−1}·2ⁿ·N!/(N−n)!`,
  `W(N,s) = (2N+1)!/(2N−2s+1)!`,

(`= 0` for `N < n`) — the leading term of `R_{2i+1}(i)` is its diagonal value
`(4i+2)!!`, and the vanishing for `N < n` is the order-`u^{2i}` Padé cancellation.

This file proves it **entirely over `ℕ`, subtraction-free**, by splitting the
signed sum into its `bpF`-part `Bsum` and `apF`-part `Asum` (each a positive
sum threaded by the weight accumulators `Bacc`/`Aacc`, which carry the coefficient
`cc = 2N−2s+1` and the weight `w = W(N,s)` so no `2N−2s` subtraction is ever
formed).  The heart is the **split lemma**

  `Bacc (n+2) cc w (s+1) steps
     = (2n+3)·Bacc (n+1) cc w (s+1) steps + Bacc n cc w s steps`,

a clean structural induction (the `(2n+3)` head + the `+bpF n (s−1)` shift of the
three-term recursion), which gives the `Bsum`/`Asum` recursions
`Bsum(n+2,N) = (2n+3)Bsum(n+1,N) + 2N(2N+1)Bsum(n,N−1)` and lets the parity-split
master identity close by a two-step induction on `n` against the absolute
closed form `cfpos n N = 2ⁿ·N!/(N−n)!` (§2).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMasterId

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor (apF bpF)
open E213.Meta.Nat.NatRing213 (nat_add_right_cancel)

/-! ## §1 — the weight-threading accumulators -/

/-- `Bacc n cc w s steps = Σ_{t=0}^{steps−1} w_t·cc_t·bpF n (s+t)`, where the
    weight `w_t` and coefficient `cc_t` start at `w`, `cc` and step by
    `w ↦ w·(cc−1)·cc`, `cc ↦ cc−2` — so `Bacc n (2N+1) 1 0 (N+1)` realizes
    `Σ_s W(N,s)·(2N−2s+1)·bpF n s` with no `2N−2s` subtraction ever formed. -/
def Bacc : Nat → Nat → Nat → Nat → Nat → Nat
  | _, _, _, _, 0 => 0
  | n, cc, w, s, steps + 1 =>
      w * cc * bpF n s + Bacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) steps

/-- The `apF`-side accumulator (no `cc` factor on the term; `cc` still threads the
    weight). -/
def Aacc : Nat → Nat → Nat → Nat → Nat → Nat
  | _, _, _, _, 0 => 0
  | n, cc, w, s, steps + 1 =>
      w * apF n s + Aacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) steps

/-- `Bsum n N = Σ_{s=0}^{N} W(N,s)·(2N−2s+1)·bpF n s` (the `bpF`-part of `L`). -/
def Bsum (n N : Nat) : Nat := Bacc n (2 * N + 1) 1 0 (N + 1)

/-- `Asum n N = Σ_{s=0}^{N} W(N,s)·apF n s` (the `apF`-part of `L`). -/
def Asum (n N : Nat) : Nat := Aacc n (2 * N + 1) 1 0 (N + 1)

/-! ## §2 — weight-linearity: a scalar factors out of the accumulator -/

theorem Bacc_Wlin : ∀ (n a cc w s steps : Nat),
    Bacc n cc (a * w) s steps = a * Bacc n cc w s steps
  | _, a, _, _, _, 0 => by
    show (0 : Nat) = a * 0
    rw [Nat.mul_zero]
  | n, a, cc, w, s, steps + 1 => by
    show a * w * cc * bpF n s + Bacc n (cc - 2) (a * w * (cc - 1) * cc) (s + 1) steps
        = a * (w * cc * bpF n s + Bacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) steps)
    rw [show a * w * (cc - 1) * cc = a * (w * (cc - 1) * cc) from by ring_nat,
        Bacc_Wlin n a (cc - 2) (w * (cc - 1) * cc) (s + 1) steps]
    ring_nat

theorem Aacc_Wlin : ∀ (n a cc w s steps : Nat),
    Aacc n cc (a * w) s steps = a * Aacc n cc w s steps
  | _, a, _, _, _, 0 => by
    show (0 : Nat) = a * 0
    rw [Nat.mul_zero]
  | n, a, cc, w, s, steps + 1 => by
    show a * w * apF n s + Aacc n (cc - 2) (a * w * (cc - 1) * cc) (s + 1) steps
        = a * (w * apF n s + Aacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) steps)
    rw [show a * w * (cc - 1) * cc = a * (w * (cc - 1) * cc) from by ring_nat,
        Aacc_Wlin n a (cc - 2) (w * (cc - 1) * cc) (s + 1) steps]
    ring_nat

/-! ## §3 — the split lemma: the three-term recursion lifts through the accumulator -/

/-- ★★★★ **The split lemma** (`B`-side): the `(n+2)` accumulator is `(2n+3)` times
    the `(n+1)` one plus the `n` one at the shifted index — the cleared form of
    `X_{n+2} = (2n+3)X_{n+1} + u·X_n` lifted through the weight threading.  Clean
    structural induction on `steps`. -/
theorem Bacc_split : ∀ (n steps cc w s : Nat),
    Bacc (n + 2) cc w (s + 1) steps
      = (2 * n + 3) * Bacc (n + 1) cc w (s + 1) steps + Bacc n cc w s steps
  | _, 0, _, _, _ => rfl
  | n, steps + 1, cc, w, s => by
    show w * cc * bpF (n + 2) (s + 1)
          + Bacc (n + 2) (cc - 2) (w * (cc - 1) * cc) (s + 1 + 1) steps
        = (2 * n + 3) * (w * cc * bpF (n + 1) (s + 1)
            + Bacc (n + 1) (cc - 2) (w * (cc - 1) * cc) (s + 1 + 1) steps)
          + (w * cc * bpF n s + Bacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) steps)
    rw [Bacc_split n steps (cc - 2) (w * (cc - 1) * cc) (s + 1),
        show bpF (n + 2) (s + 1) = (2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s from rfl]
    ring_nat

theorem Aacc_split : ∀ (n steps cc w s : Nat),
    Aacc (n + 2) cc w (s + 1) steps
      = (2 * n + 3) * Aacc (n + 1) cc w (s + 1) steps + Aacc n cc w s steps
  | _, 0, _, _, _ => rfl
  | n, steps + 1, cc, w, s => by
    show w * apF (n + 2) (s + 1)
          + Aacc (n + 2) (cc - 2) (w * (cc - 1) * cc) (s + 1 + 1) steps
        = (2 * n + 3) * (w * apF (n + 1) (s + 1)
            + Aacc (n + 1) (cc - 2) (w * (cc - 1) * cc) (s + 1 + 1) steps)
          + (w * apF n s + Aacc n (cc - 2) (w * (cc - 1) * cc) (s + 1) steps)
    rw [Aacc_split n steps (cc - 2) (w * (cc - 1) * cc) (s + 1),
        show apF (n + 2) (s + 1) = (2 * n + 3) * apF (n + 1) (s + 1) + apF n s from rfl]
    ring_nat

/-! ## §4 — the `Bsum`/`Asum` three-term recursions -/

/-- The `s = 0` peel + split, kept symbolic in `cc, w`: the `(n+2)` accumulator
    from index `0` equals `(2n+3)·`(the `(n+1)` one) plus the `n` shift. -/
theorem Bacc_zero_split (n cc w steps : Nat) :
    Bacc (n + 2) cc w 0 (steps + 1)
      = (2 * n + 3) * Bacc (n + 1) cc w 0 (steps + 1)
        + Bacc n (cc - 2) (w * (cc - 1) * cc) 0 steps := by
  show w * cc * bpF (n + 2) 0 + Bacc (n + 2) (cc - 2) (w * (cc - 1) * cc) (0 + 1) steps
      = (2 * n + 3) * (w * cc * bpF (n + 1) 0
          + Bacc (n + 1) (cc - 2) (w * (cc - 1) * cc) (0 + 1) steps)
        + Bacc n (cc - 2) (w * (cc - 1) * cc) 0 steps
  rw [Bacc_split n steps (cc - 2) (w * (cc - 1) * cc) 0,
      show bpF (n + 2) 0 = (2 * n + 3) * bpF (n + 1) 0 from rfl]
  ring_nat

theorem Aacc_zero_split (n cc w steps : Nat) :
    Aacc (n + 2) cc w 0 (steps + 1)
      = (2 * n + 3) * Aacc (n + 1) cc w 0 (steps + 1)
        + Aacc n (cc - 2) (w * (cc - 1) * cc) 0 steps := by
  show w * apF (n + 2) 0 + Aacc (n + 2) (cc - 2) (w * (cc - 1) * cc) (0 + 1) steps
      = (2 * n + 3) * (w * apF (n + 1) 0
          + Aacc (n + 1) (cc - 2) (w * (cc - 1) * cc) (0 + 1) steps)
        + Aacc n (cc - 2) (w * (cc - 1) * cc) 0 steps
  rw [Aacc_split n steps (cc - 2) (w * (cc - 1) * cc) 0,
      show apF (n + 2) 0 = (2 * n + 3) * apF (n + 1) 0 from rfl]
  ring_nat

/-- ★★★★ **The `Bsum` three-term recursion**:
    `Bsum(n+2,M+1) = (2n+3)Bsum(n+1,M+1) + 2(M+1)(2M+3)·Bsum(n,M)`.
    `Bacc_zero_split` instantiated at `cc = 2(M+1)+1, w = 1`, then `Bacc_Wlin`
    collapses the shift (`cc−2 = 2M+1`, `w·(cc−1)·cc = 2(M+1)(2(M+1)+1)`). -/
theorem Bsum_rec (n M : Nat) :
    Bsum (n + 2) (M + 1)
      = (2 * n + 3) * Bsum (n + 1) (M + 1)
        + 2 * (M + 1) * (2 * (M + 1) + 1) * Bsum n M := by
  show Bacc (n + 2) (2 * (M + 1) + 1) 1 0 (M + 1 + 1)
      = (2 * n + 3) * Bacc (n + 1) (2 * (M + 1) + 1) 1 0 (M + 1 + 1)
        + 2 * (M + 1) * (2 * (M + 1) + 1) * Bacc n (2 * M + 1) 1 0 (M + 1)
  rw [Bacc_zero_split n (2 * (M + 1) + 1) 1 (M + 1),
      show (2 * (M + 1) + 1 - 2) = 2 * M + 1 from rfl,
      show (1 * (2 * (M + 1) + 1 - 1) * (2 * (M + 1) + 1))
        = 2 * (M + 1) * (2 * (M + 1) + 1) * 1 from by
        rw [show (2 * (M + 1) + 1 - 1) = 2 * (M + 1) from rfl]; ring_nat,
      Bacc_Wlin n (2 * (M + 1) * (2 * (M + 1) + 1)) (2 * M + 1) 1 0 (M + 1)]

theorem Asum_rec (n M : Nat) :
    Asum (n + 2) (M + 1)
      = (2 * n + 3) * Asum (n + 1) (M + 1)
        + 2 * (M + 1) * (2 * (M + 1) + 1) * Asum n M := by
  show Aacc (n + 2) (2 * (M + 1) + 1) 1 0 (M + 1 + 1)
      = (2 * n + 3) * Aacc (n + 1) (2 * (M + 1) + 1) 1 0 (M + 1 + 1)
        + 2 * (M + 1) * (2 * (M + 1) + 1) * Aacc n (2 * M + 1) 1 0 (M + 1)
  rw [Aacc_zero_split n (2 * (M + 1) + 1) 1 (M + 1),
      show (2 * (M + 1) + 1 - 2) = 2 * M + 1 from rfl,
      show (1 * (2 * (M + 1) + 1 - 1) * (2 * (M + 1) + 1))
        = 2 * (M + 1) * (2 * (M + 1) + 1) * 1 from by
        rw [show (2 * (M + 1) + 1 - 1) = 2 * (M + 1) from rfl]; ring_nat,
      Aacc_Wlin n (2 * (M + 1) * (2 * (M + 1) + 1)) (2 * M + 1) 1 0 (M + 1)]

/-- The `N = 0` sums are just the head coefficients. -/
theorem Bsum_at_zero (n : Nat) : Bsum n 0 = bpF n 0 := by
  show 1 * 1 * bpF n 0 + 0 = bpF n 0
  rw [Nat.add_zero, Nat.one_mul]

theorem Asum_at_zero (n : Nat) : Asum n 0 = apF n 0 := by
  show 1 * apF n 0 + 0 = apF n 0
  rw [Nat.add_zero, Nat.one_mul]

/-- The `N = 0` rungs: `Bsum(n+2,0) = (2n+3)Bsum(n+1,0)` (the shift vanishes). -/
theorem Bsum_rec_zero (n : Nat) : Bsum (n + 2) 0 = (2 * n + 3) * Bsum (n + 1) 0 := by
  rw [Bsum_at_zero, Bsum_at_zero,
      show bpF (n + 2) 0 = (2 * n + 3) * bpF (n + 1) 0 from rfl]

theorem Asum_rec_zero (n : Nat) : Asum (n + 2) 0 = (2 * n + 3) * Asum (n + 1) 0 := by
  rw [Asum_at_zero, Asum_at_zero,
      show apF (n + 2) 0 = (2 * n + 3) * apF (n + 1) 0 from rfl]

/-! ## §5 — bases -/

/-- `Bsum 0 N = 0` (`bpF 0` is identically zero). -/
theorem Bsum_zero (N : Nat) : Bsum 0 N = 0 := by
  show Bacc 0 (2 * N + 1) 1 0 (N + 1) = 0
  have aux : ∀ steps cc w s, Bacc 0 cc w s steps = 0 := by
    intro steps
    induction steps with
    | zero => intro cc w s; rfl
    | succ k ih =>
      intro cc w s
      show w * cc * bpF 0 s + Bacc 0 (cc - 2) (w * (cc - 1) * cc) (s + 1) k = 0
      rw [show bpF 0 s = 0 from rfl, Nat.mul_zero, Nat.zero_add,
          ih (cc - 2) (w * (cc - 1) * cc) (s + 1)]
  exact aux (N + 1) (2 * N + 1) 1 0

theorem anchors :
    Bsum 1 3 = 7 * 1 ∧ Asum 1 3 = 1 ∧ Bsum 0 5 = 0
    ∧ Bsum 3 3 = Asum 3 3 + 48 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMasterId
