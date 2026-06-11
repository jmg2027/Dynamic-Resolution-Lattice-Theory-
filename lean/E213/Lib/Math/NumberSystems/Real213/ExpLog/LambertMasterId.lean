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

/-- `Asum 0 N = 1`, `Bsum 1 N = 2N+1`, `Asum 1 N = 1` — the bases (tails vanish
    because `apF/bpF 0/1 (s+1) = 0`). -/
theorem Asum_zero (N : Nat) : Asum 0 N = 1 := by
  show Aacc 0 (2 * N + 1) 1 0 (N + 1) = 1
  have aux : ∀ steps cc w s, Aacc 0 cc w (s + 1) steps = 0 := by
    intro steps
    induction steps with
    | zero => intro cc w s; rfl
    | succ k ih =>
      intro cc w s
      show w * apF 0 (s + 1) + Aacc 0 (cc - 2) (w * (cc - 1) * cc) (s + 1 + 1) k = 0
      rw [show apF 0 (s + 1) = 0 from rfl, Nat.mul_zero, Nat.zero_add,
          ih (cc - 2) (w * (cc - 1) * cc) (s + 1)]
  show 1 * apF 0 0 + Aacc 0 (2 * N + 1 - 2) (1 * (2 * N + 1 - 1) * (2 * N + 1)) (0 + 1) N = 1
  rw [show apF 0 0 = 1 from rfl, Nat.mul_one,
      aux N (2 * N + 1 - 2) (1 * (2 * N + 1 - 1) * (2 * N + 1)) 0, Nat.add_zero]

theorem Bsum_one (N : Nat) : Bsum 1 N = 2 * N + 1 := by
  show Bacc 1 (2 * N + 1) 1 0 (N + 1) = 2 * N + 1
  have aux : ∀ steps cc w s, Bacc 1 cc w (s + 1) steps = 0 := by
    intro steps
    induction steps with
    | zero => intro cc w s; rfl
    | succ k ih =>
      intro cc w s
      show w * cc * bpF 1 (s + 1) + Bacc 1 (cc - 2) (w * (cc - 1) * cc) (s + 1 + 1) k = 0
      rw [show bpF 1 (s + 1) = 0 from rfl, Nat.mul_zero, Nat.zero_add,
          ih (cc - 2) (w * (cc - 1) * cc) (s + 1)]
  show 1 * (2 * N + 1) * bpF 1 0 + Bacc 1 (2 * N + 1 - 2) (1 * (2 * N + 1 - 1) * (2 * N + 1)) (0 + 1) N
      = 2 * N + 1
  rw [show bpF 1 0 = 1 from rfl, Nat.mul_one,
      aux N (2 * N + 1 - 2) (1 * (2 * N + 1 - 1) * (2 * N + 1)) 0, Nat.add_zero, Nat.one_mul]

theorem Asum_one (N : Nat) : Asum 1 N = 1 := by
  show Aacc 1 (2 * N + 1) 1 0 (N + 1) = 1
  have aux : ∀ steps cc w s, Aacc 1 cc w (s + 1) steps = 0 := by
    intro steps
    induction steps with
    | zero => intro cc w s; rfl
    | succ k ih =>
      intro cc w s
      show w * apF 1 (s + 1) + Aacc 1 (cc - 2) (w * (cc - 1) * cc) (s + 1 + 1) k = 0
      rw [show apF 1 (s + 1) = 0 from rfl, Nat.mul_zero, Nat.zero_add,
          ih (cc - 2) (w * (cc - 1) * cc) (s + 1)]
  show 1 * apF 1 0 + Aacc 1 (2 * N + 1 - 2) (1 * (2 * N + 1 - 1) * (2 * N + 1)) (0 + 1) N = 1
  rw [show apF 1 0 = 1 from rfl, Nat.mul_one,
      aux N (2 * N + 1 - 2) (1 * (2 * N + 1 - 1) * (2 * N + 1)) 0, Nat.add_zero]

/-! ## §6 — the closed form `cfpos n N = 2ⁿ·N!/(N−n)!` -/

/-- `descFac N n = N(N−1)⋯(N−n+1)` (`= N!/(N−n)!`), top-peeled so only a single
    `N−1` subtraction appears. -/
def descFac : Nat → Nat → Nat
  | _, 0 => 1
  | N, n + 1 => N * descFac (N - 1) n

/-- `(M−1)−n = M−(n+1)` (pure; `Nat.sub_sub` carries `propext`). -/
theorem sub_one_sub (M : Nat) : ∀ n, M - 1 - n = M - (n + 1)
  | 0 => rfl
  | n + 1 => by
    show M - 1 - n - 1 = M - (n + 1) - 1
    rw [sub_one_sub M n]

/-- The descending product vanishes past `M`. -/
theorem descFac_vanish : ∀ M n, M < n → descFac M n = 0
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => by
    show 0 * descFac (0 - 1) _ = 0
    rw [Nat.zero_mul]
  | M + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | M + 1, n + 1, h => by
    show (M + 1) * descFac (M + 1 - 1) n = 0
    rw [show (M + 1 - 1) = M from rfl,
        descFac_vanish M n (Nat.lt_of_succ_lt_succ h), Nat.mul_zero]

/-- **Bottom peel**: `descFac M (n+1) = (M−n)·descFac M n`, by induction on `n`. -/
theorem descFac_bottom : ∀ M n, descFac M (n + 1) = (M - n) * descFac M n
  | M, 0 => by
    show M * descFac (M - 1) 0 = (M - 0) * descFac M 0
    rw [show descFac (M - 1) 0 = 1 from rfl, show descFac M 0 = 1 from rfl,
        Nat.sub_zero, Nat.mul_one]
  | M, n + 1 => by
    show M * descFac (M - 1) (n + 1) = (M - (n + 1)) * (M * descFac (M - 1) n)
    rw [descFac_bottom (M - 1) n, sub_one_sub M n]
    ring_nat

/-- `(M − n) + n = M` for `n ≤ M`. -/
theorem sub_add_recover {n M : Nat} (h : n ≤ M) : M - n + n = M := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, Nat.add_comm n k, E213.Tactic.NatHelper.add_sub_cancel_right k n,
      Nat.add_comm k n]

/-- Coefficient absorption: `descFac M n·(2(M−n)+2n+3) = descFac M n·(2M+3)` —
    either `n ≤ M` (so `(M−n)+n = M`) or `descFac M n = 0`. -/
theorem descFac_coeff (M n : Nat) :
    descFac M n * (2 * (M - n) + 2 * n + 3) = descFac M n * (2 * M + 3) := by
  rcases Nat.lt_or_ge M n with hlt | hge
  · rw [descFac_vanish M n hlt, Nat.zero_mul, Nat.zero_mul]
  · have h : 2 * (M - n) + 2 * n = 2 * M := by
      rw [show 2 * (M - n) + 2 * n = 2 * (M - n + n) from by ring_nat, sub_add_recover hge]
    rw [show 2 * (M - n) + 2 * n + 3 = 2 * (M - n) + 2 * n + 3 from rfl, h]

/-- The closed form `cfpos n N = 2ⁿ·N!/(N−n)!` (absolute value of the master
    constant; `= 0` for `N < n` — the Padé cancellation). -/
def cfpos (n N : Nat) : Nat := 2 ^ n * descFac N n

theorem cfpos_zero (N : Nat) : cfpos 0 N = 1 := rfl

theorem cfpos_one (N : Nat) : cfpos 1 N = 2 * N := by
  show 2 ^ 1 * descFac N 1 = 2 * N
  rw [show descFac N 1 = N * 1 from rfl, Nat.mul_one, Nat.pow_one]

/-- `cfpos (n+1) 0 = 0` (the descending product from `0` past the head vanishes). -/
theorem cfpos_zero_pos (n : Nat) : cfpos (n + 1) 0 = 0 := by
  show 2 ^ (n + 1) * descFac 0 (n + 1) = 0
  rw [descFac_vanish 0 (n + 1) (Nat.succ_pos n), Nat.mul_zero]

/-- ★★★★★ **The moved recursion** (the `binom_absorption` analog):
    `cfpos(n+2,N) + (2n+3)cfpos(n+1,N) = 2N(2N+1)cfpos(n,N−1)`.  Top-peel both
    `descFac N` factors, `descFac_bottom` on the `(n+1)` one, then `descFac_coeff`
    (`2(N−1−n)+(2n+3) = 2N+1`). -/
theorem cfpos_moved (n N : Nat) :
    cfpos (n + 2) N + (2 * n + 3) * cfpos (n + 1) N
      = 2 * N * (2 * N + 1) * cfpos n (N - 1) := by
  cases N with
  | zero =>
    show cfpos (n + 2) 0 + (2 * n + 3) * cfpos (n + 1) 0
        = 2 * 0 * (2 * 0 + 1) * cfpos n (0 - 1)
    rw [cfpos_zero_pos (n + 1), cfpos_zero_pos n, Nat.mul_zero,
        show 2 * 0 * (2 * 0 + 1) = 0 from rfl, Nat.zero_mul, Nat.add_zero]
  | succ M =>
    show 2 ^ (n + 2) * descFac (M + 1) (n + 2)
          + (2 * n + 3) * (2 ^ (n + 1) * descFac (M + 1) (n + 1))
        = 2 * (M + 1) * (2 * (M + 1) + 1) * (2 ^ n * descFac (M + 1 - 1) n)
    rw [show descFac (M + 1) (n + 2) = (M + 1) * descFac (M + 1 - 1) (n + 1) from rfl,
        show descFac (M + 1) (n + 1) = (M + 1) * descFac (M + 1 - 1) n from rfl,
        show (M + 1 - 1) = M from rfl, descFac_bottom M n,
        show (2 : Nat) ^ (n + 2) = 2 ^ (n + 1) * 2 from by rw [Nat.pow_succ],
        show (2 : Nat) ^ (n + 1) = 2 ^ n * 2 from by rw [Nat.pow_succ]]
    rw [show 2 ^ n * 2 * 2 * ((M + 1) * ((M - n) * descFac M n))
          + (2 * n + 3) * (2 ^ n * 2 * ((M + 1) * descFac M n))
        = 2 ^ n * 2 * (M + 1) * (descFac M n * (2 * (M - n) + 2 * n + 3)) from by ring_nat,
        descFac_coeff M n,
        show 2 * (M + 1) * (2 * (M + 1) + 1) * (2 ^ n * descFac M n)
          = 2 ^ n * 2 * (M + 1) * (descFac M n * (2 * M + 3)) from by ring_nat]

/-! ## §7 — the master identity (parity-split, subtraction-free) -/

/-- At resolution `N = 0` the two sums coincide past the head (`cfpos (n+1) 0 = 0`):
    `Bsum (n+1) 0 = Asum (n+1) 0`, by induction on `n` via the `N = 0` recursions. -/
theorem bsum_asum_zero : ∀ n, Bsum (n + 1) 0 = Asum (n + 1) 0
  | 0 => by rw [Bsum_one, Asum_one]
  | n + 1 => by
    rw [Bsum_rec_zero n, Asum_rec_zero n, bsum_asum_zero n]

/-- The even rungs (`Bsum + cfpos = Asum`) and odd rungs (`Asum + cfpos = Bsum`),
    proved together by a paired two-step induction on `k` (the `(2k, 2k+1)`
    block): the step uses the `Bsum`/`Asum` three-term recursions and
    `cfpos_moved`, all subtraction-free.  Returns both the even-at-`2k` and
    odd-at-`2k+1` families for every `N`. -/
theorem master_pair : ∀ k,
    (∀ N, Bsum (2 * k) N + cfpos (2 * k) N = Asum (2 * k) N)
    ∧ (∀ N, Asum (2 * k + 1) N + cfpos (2 * k + 1) N = Bsum (2 * k + 1) N)
  | 0 => by
    refine ⟨fun N => ?_, fun N => ?_⟩
    · show Bsum 0 N + cfpos 0 N = Asum 0 N
      rw [Bsum_zero, cfpos_zero, Asum_zero]
    · show Asum 1 N + cfpos 1 N = Bsum 1 N
      rw [Asum_one, cfpos_one, Bsum_one]
      rw [Nat.add_comm 1 (2 * N)]
  | k + 1 => by
    obtain ⟨ihEv, ihOd⟩ := master_pair k
    have hev : ∀ N, Bsum (2 * (k + 1)) N + cfpos (2 * (k + 1)) N = Asum (2 * (k + 1)) N := by
      intro N
      cases N with
      | zero =>
        show Bsum (2 * k + 2) 0 + cfpos (2 * k + 2) 0 = Asum (2 * k + 2) 0
        rw [show cfpos (2 * k + 2) 0 = 0 from cfpos_zero_pos (2 * k + 1), Nat.add_zero,
            show Bsum (2 * k + 2) 0 = Asum (2 * k + 2) 0 from bsum_asum_zero (2 * k + 1)]
      | succ M =>
        show Bsum (2 * k + 2) (M + 1) + cfpos (2 * k + 2) (M + 1) = Asum (2 * k + 2) (M + 1)
        rw [Bsum_rec (2 * k) M, Asum_rec (2 * k) M]
        have hmov := cfpos_moved (2 * k) (M + 1)
        rw [show (M + 1 - 1) = M from rfl] at hmov
        -- (2k+3)Bsum(2k+1,M+1) + W Bsum(2k,M) + cfpos(2k+2,M+1) = (2k+3)Asum(2k+1,M+1) + W Asum(2k,M)
        rw [show Bsum (2 * k + 1) (M + 1) = Asum (2 * k + 1) (M + 1) + cfpos (2 * k + 1) (M + 1)
              from (ihOd (M + 1)).symm,
            show Asum (2 * k) M = Bsum (2 * k) M + cfpos (2 * k) M
              from (ihEv M).symm]
        rw [show (2 * (2 * k) + 3) * (Asum (2 * k + 1) (M + 1) + cfpos (2 * k + 1) (M + 1))
                + 2 * (M + 1) * (2 * (M + 1) + 1) * Bsum (2 * k) M + cfpos (2 * k + 2) (M + 1)
              = (2 * (2 * k) + 3) * Asum (2 * k + 1) (M + 1)
                + 2 * (M + 1) * (2 * (M + 1) + 1) * Bsum (2 * k) M
                + (cfpos (2 * k + 2) (M + 1) + (2 * (2 * k) + 3) * cfpos (2 * k + 1) (M + 1))
              from by ring_nat,
            hmov,
            show (2 : Nat) * (M + 1) * (2 * (M + 1) + 1) * (Bsum (2 * k) M + cfpos (2 * k) M)
              = 2 * (M + 1) * (2 * (M + 1) + 1) * Bsum (2 * k) M
                + 2 * (M + 1) * (2 * (M + 1) + 1) * cfpos (2 * k) M from by ring_nat]
        ring_nat
    refine ⟨?_, ?_⟩
    · intro N; exact hev N
    · intro N
      cases N with
      | zero =>
        show Asum (2 * (k + 1) + 1) 0 + cfpos (2 * (k + 1) + 1) 0 = Bsum (2 * (k + 1) + 1) 0
        rw [show cfpos (2 * (k + 1) + 1) 0 = 0 from cfpos_zero_pos (2 * (k + 1)), Nat.add_zero,
            show Asum (2 * (k + 1) + 1) 0 = Bsum (2 * (k + 1) + 1) 0
              from (bsum_asum_zero (2 * (k + 1))).symm]
      | succ M =>
        show Asum (2 * (k + 1) + 1) (M + 1) + cfpos (2 * (k + 1) + 1) (M + 1)
            = Bsum (2 * (k + 1) + 1) (M + 1)
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring_nat,
            Bsum_rec (2 * k + 1) M, Asum_rec (2 * k + 1) M]
        have hmov := cfpos_moved (2 * k + 1) (M + 1)
        rw [show (M + 1 - 1) = M from rfl] at hmov
        rw [show Asum (2 * k + 2) (M + 1) = Bsum (2 * k + 2) (M + 1) + cfpos (2 * k + 2) (M + 1)
              from (hev (M + 1)).symm,
            show Bsum (2 * k + 1) M = Asum (2 * k + 1) M + cfpos (2 * k + 1) M
              from (ihOd M).symm]
        rw [show (2 * (2 * k + 1) + 3) * (Bsum (2 * k + 2) (M + 1) + cfpos (2 * k + 2) (M + 1))
                + 2 * (M + 1) * (2 * (M + 1) + 1) * Asum (2 * k + 1) M
                + cfpos ((2 * k + 1) + 2) (M + 1)
              = (2 * (2 * k + 1) + 3) * Bsum (2 * k + 2) (M + 1)
                + 2 * (M + 1) * (2 * (M + 1) + 1) * Asum (2 * k + 1) M
                + (cfpos ((2 * k + 1) + 2) (M + 1)
                  + (2 * (2 * k + 1) + 3) * cfpos (2 * k + 2) (M + 1))
              from by ring_nat]
        rw [show (2 * k + 2) = ((2 * k + 1) + 1) from rfl] at hmov ⊢
        rw [hmov,
            show (2 : Nat) * (M + 1) * (2 * (M + 1) + 1) * (Asum (2 * k + 1) M + cfpos (2 * k + 1) M)
              = 2 * (M + 1) * (2 * (M + 1) + 1) * Asum (2 * k + 1) M
                + 2 * (M + 1) * (2 * (M + 1) + 1) * cfpos (2 * k + 1) M from by ring_nat]
        ring_nat

/-- ★★★★★ **The master identity, odd levels**: `Asum (2k+1) N + cfpos (2k+1) N =
    Bsum (2k+1) N` — the `bpF`-sum exceeds the `apF`-sum by exactly the closed
    form (`= 0` for `N < 2k+1`, the order-`u^{2k}` Padé cancellation). -/
theorem master_odd (k N : Nat) :
    Asum (2 * k + 1) N + cfpos (2 * k + 1) N = Bsum (2 * k + 1) N :=
  (master_pair k).2 N

/-- The even levels: `Bsum (2k) N + cfpos (2k) N = Asum (2k) N`. -/
theorem master_even (k N : Nat) :
    Bsum (2 * k) N + cfpos (2 * k) N = Asum (2 * k) N :=
  (master_pair k).1 N

/-- ★★★★ **The diagonal**: `Bsum (2i+1) (2i+1) = Asum (2i+1) (2i+1) + cfpos (2i+1) (2i+1)`,
    and `cfpos (2i+1) (2i+1) = (4i+2)!!` (`= 2^{2i+1}(2i+1)!`) — the leading
    coefficient of the truncated coth-residual `R_{2i+1}(i)`.  This is the
    Padé-flip value `LowerBase` consumes. -/
theorem master_diagonal (i : Nat) :
    Bsum (2 * i + 1) (2 * i + 1) = Asum (2 * i + 1) (2 * i + 1) + cfpos (2 * i + 1) (2 * i + 1) :=
  (master_odd i (2 * i + 1)).symm

theorem anchors :
    Bsum 1 3 = 7 ∧ Asum 1 3 = 1 ∧ Bsum 0 5 = 0
    ∧ Bsum 3 3 = Asum 3 3 + 48 ∧ cfpos 3 3 = 48 ∧ cfpos 5 5 = 3840
    ∧ master_even 1 4 = master_even 1 4 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMasterId
