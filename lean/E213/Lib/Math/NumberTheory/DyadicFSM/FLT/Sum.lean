import E213.Meta.Nat.AddMod213
/-!
# Σ-sum infrastructure (213-native) — FLT prerequisite

Recursive `sumTo n f := f 0 + f 1 + ... + f (n - 1)` (exclusive
upper-bound, so `sumTo 0 f = 0` and `sumTo (n+1) f = sumTo n f + f n`).

Provides the modular-arithmetic identity needed for the binomial-mod-p
argument:

  `(sumTo n f) % p = sumTo n (fun k => f k % p) % p`

— mod-p distribution over sums.  Used by the FLT freshman's-dream
proof to reduce `(a + 1)^p` via term-by-term mod-p reduction.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod)

/-- Recursive Σ over `[0, n)`:  `sumTo n f = f 0 + f 1 + ... + f (n-1)`.
    `sumTo 0 f = 0`, `sumTo (n+1) f = sumTo n f + f n`. -/
def sumTo : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

@[simp] theorem sumTo_zero (f : Nat → Nat) : sumTo 0 f = 0 := rfl

@[simp] theorem sumTo_succ (n : Nat) (f : Nat → Nat) :
    sumTo (n + 1) f = sumTo n f + f n := rfl

/-- Smoke: `sumTo 5 (fun k => k + 1) = 1 + 2 + 3 + 4 + 5 = 15`. -/
theorem sumTo_smoke : sumTo 5 (fun k => k + 1) = 15 := by decide

/-- ★ **Mod-p distributes over Σ**:
    `(sumTo n f) % p = sumTo n (fun k => f k % p) % p`.

    By induction on `n`, using `add_mod_gen` at each step.  PURE. -/
theorem sumTo_mod (p : Nat) :
    ∀ n (f : Nat → Nat),
      (sumTo n f) % p = (sumTo n (fun k => f k % p)) % p
  | 0, _ => rfl
  | n + 1, f => by
    show (sumTo n f + f n) % p = (sumTo n (fun k => f k % p) + f n % p) % p
    -- Apply add_mod_gen forward on both sides, IH on the sum part,
    -- then collapse `(f n % p) % p = f n % p` via mod_mod.
    rw [add_mod_gen (sumTo n f) (f n) p,
        sumTo_mod p n f,
        add_mod_gen (sumTo n (fun k => f k % p)) (f n % p) p,
        mod_mod (f n) p]

/-- ★ **If every term is ≡ 0 mod p, the sum is ≡ 0 mod p**.
    Useful for the binomial-mod-p argument: middle terms
    `C(p, k) · a^{p-k}` for `1 ≤ k ≤ p-1` all have `C(p, k) ≡ 0`,
    so their sum vanishes mod p.  PURE. -/
theorem sumTo_eq_zero_of_all_zero (p : Nat) :
    ∀ n (f : Nat → Nat),
      (∀ k, k < n → (f k) % p = 0) → (sumTo n f) % p = 0
  | 0, _, _ => rfl
  | n + 1, f, h => by
    show (sumTo n f + f n) % p = 0
    rw [add_mod_gen (sumTo n f) (f n) p]
    have hn : (f n) % p = 0 := h n (Nat.lt_succ_self _)
    have hrec : (sumTo n f) % p = 0 :=
      sumTo_eq_zero_of_all_zero p n f (fun k hk => h k (Nat.lt_succ_of_lt hk))
    rw [hn, hrec]
    rfl

/-- Term-wise rewrite: extract a single term from a sum.
    `sumTo (n + 1) f = sumTo n f + f n`.  (Same as `sumTo_succ`,
    re-stated for clarity in chained rewrites.) -/
theorem sumTo_extract_last (n : Nat) (f : Nat → Nat) :
    sumTo (n + 1) f = sumTo n f + f n := rfl

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
