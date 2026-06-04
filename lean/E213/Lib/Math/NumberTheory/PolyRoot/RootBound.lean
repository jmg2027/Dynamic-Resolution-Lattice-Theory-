import E213.Lib.Math.NumberTheory.PolyRoot.FactorTheorem
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid

/-!
# PolyRoot/RootBound — Lagrange's root bound (eval-vanishing form)

Building on the factor theorem (`factor_eval`) and Euclid's lemma over `ℤ` (`int_euclid`):
if a polynomial `f` has more pairwise-distinct (mod `p`) roots than its length, then `eval f`
vanishes mod `p` **everywhere** — in particular at `0`, where `eval f 0` is the constant
coefficient.  Contrapositive: a polynomial whose constant coefficient is `≢ 0 mod p` has
fewer distinct roots than its length.

  * `root_transfer` — a root `s ≠ r` of `f` is a root of `quot r f` (mod `p`).
  * ★★★★ `eval_zero` — distinct roots `rs` of `f` with `f.length ≤ rs.length` ⟹
    `∀ x, p ∣ eval f x`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PolyRoot

/-- `s ≠ r mod p`, both roots of `f` ⟹ `s` is a root of `quot r f` (mod `p`). -/
theorem root_transfer (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (f : List Int) (r s : Int) (hr : (p : Int) ∣ eval f r) (hs : (p : Int) ∣ eval f s)
    (hsr : ¬ (p : Int) ∣ (s - r)) : (p : Int) ∣ eval (quot r f) s := by
  have hfact : eval f s - eval f r = (s - r) * eval (quot r f) s := factor_eval r f s
  have hd : (p : Int) ∣ (s - r) * eval (quot r f) s := hfact ▸ dvd_sub' hs hr
  exact int_euclid p hp hpr (s - r) (eval (quot r f) s) hd hsr

/-- `¬ p ∣ (r − s)` ⟹ `¬ p ∣ (s − r)` (divisibility is sign-blind). -/
private theorem not_dvd_sub_comm {a x y : Int} (h : ¬ a ∣ (x - y)) : ¬ a ∣ (y - x) := by
  intro hd
  apply h
  obtain ⟨c, hc⟩ := hd
  exact ⟨-c, by rw [E213.Meta.Int213.mul_neg, ← hc]; ring_intZ⟩

/-- ★★★★ **Lagrange's root bound (eval-vanishing form).**  If `rs` is pairwise-distinct mod
    `p` and every element is a root of `f` mod `p`, and `f.length ≤ rs.length`, then `f`
    vanishes mod `p` at every point.  By fuel-induction on `f.length`: peel a root `r`,
    transfer the rest to `quot r f` (one shorter), recurse, then reassemble by the factor
    identity. -/
theorem eval_zero (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ (n : Nat) (f : List Int), f.length ≤ n → ∀ (rs : List Int),
      rs.Pairwise (fun a b => ¬ (p : Int) ∣ (a - b)) →
      (∀ r ∈ rs, (p : Int) ∣ eval f r) → f.length ≤ rs.length →
      ∀ x : Int, (p : Int) ∣ eval f x := by
  intro n
  induction n with
  | zero =>
    intro f hf _ _ _ _ x
    have hfnil : f = [] := List.length_eq_zero.mp (Nat.le_zero.mp hf)
    rw [hfnil, eval_nil]; exact ⟨0, rfl⟩
  | succ n ih =>
    intro f hf rs hdist hroots hlen x
    cases f with
    | nil => rw [eval_nil]; exact ⟨0, rfl⟩
    | cons a as =>
      cases rs with
      | nil =>
        rw [List.length_cons] at hlen
        exact absurd hlen (Nat.not_succ_le_zero as.length)
      | cons r rs' =>
        have hr : (p : Int) ∣ eval (a :: as) r := hroots r (List.mem_cons_self r rs')
        obtain ⟨hrhead, hdist'⟩ := List.pairwise_cons.mp hdist
        have hqroots : ∀ s ∈ rs', (p : Int) ∣ eval (quot r (a :: as)) s := by
          intro s hs
          have hsroot : (p : Int) ∣ eval (a :: as) s := hroots s (List.mem_cons_of_mem r hs)
          exact root_transfer p hp hpr (a :: as) r s hr hsroot (not_dvd_sub_comm (hrhead s hs))
        have hlen' : as.length ≤ rs'.length := by
          have h1 := hlen
          rw [List.length_cons, List.length_cons] at h1
          exact Nat.le_of_succ_le_succ h1
        have hffuel : as.length ≤ n := by
          have h1 := hf
          rw [List.length_cons] at h1
          exact Nat.le_of_succ_le_succ h1
        have hqlen : (quot r (a :: as)).length ≤ rs'.length := by
          rw [quot_length, List.length_cons, Nat.succ_sub_one]; exact hlen'
        have hqfuel : (quot r (a :: as)).length ≤ n := by
          rw [quot_length, List.length_cons, Nat.succ_sub_one]; exact hffuel
        have hqzero := ih (quot r (a :: as)) hqfuel rs' hdist' hqroots hqlen
        have heq : eval (a :: as) x
            = eval (a :: as) r + (x - r) * eval (quot r (a :: as)) x := by
          rw [← factor_eval r (a :: as) x]; ring_intZ
        rw [heq]
        exact dvd_add' hr (dvd_mul_left' (hqzero x) (x - r))

end E213.Lib.Math.NumberTheory.PolyRoot
