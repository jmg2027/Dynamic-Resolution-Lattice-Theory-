import E213.Lib.Math.Combinatorics.BinomialInversion
import E213.Lib.Math.Combinatorics.StirlingOrthogonality
import E213.Lib.Math.Combinatorics.StirlingOrthogonality2
import E213.Lib.Math.NumberTheory.DirichletIdentities
import E213.Meta.Int213.PolyIntMTactic

/-!
# Incidence-algebra inversion — one antipode under the two cuts of ℕ (∅-axiom)

ℕ carries two comultiplications (cuts): the **additive** cut
`Δ_+ : n ↦ Σ_{i+j=n} i⊗j` and the **multiplicative** cut
`Δ_× : n ↦ Σ_{d·e=n} d⊗e`. Each cut's
convolution has an **antipode**, and inversion against the structure element is the
*same* incidence-algebra move (Rota 1964) read through the two cuts:

  · **additive** — the Pascal incidence matrix `C(n,k)` (poset `(ℕ,≤)`), antipode the
    signed binomial `(−1)^{n−k}C(n,k)`; transform = binomial transform, inverse =
    binomial inversion;
  · **multiplicative** — the divisibility zeta `ζ` (poset `(ℕ,∣)`), antipode the Möbius
    `μ`; transform = divisor sum, inverse = Möbius inversion.

The corpus closed each inversion separately
(`Combinatorics.BinomialInversion.binomial_inversion`,
`NumberTheory.MobiusInversion.mobius_inversion`). This file exhibits the **shared
engine**: a single abstract inversion law `inversion_from_orthogonality` — a
lower-triangular unit matrix `M` with an antipode `S` satisfying the matrix
orthogonality `Σ_k S(n,k)·M(k,i) = δ(n,i)` inverts the transform `g = M·f` to
`f = S·g` — instantiated on the **additive** cut (binomial), and the same
incidence-algebra inverse-element argument on the **multiplicative** cut (Möbius),
re-derived from the Dirichlet ring laws (`μ ∗ 1 = ε`, associativity, unit).

Both faces are the one antipode of an incidence algebra; the cut chooses the poset.

Companion essay: `theory/essays/proof_isa/incidence_inversion.md`.
-/

namespace E213.Lib.Math.IncidenceInversion

open E213.Lib.Math.Combinatorics.BinomialInversion
  (sumZ sumZ_congr sumZ_mul_left sumZ_swap sumZ_delta_collapse sumZ_add_range
   sumZ_const_zero delta sb T binomial_orthogonality)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_eq_zero_of_lt)
open E213.Lib.Math.NumberTheory.DirichletConvolution (dconv dirichlet_assoc)
open E213.Lib.Math.NumberTheory.DirichletIdentities
  (eps mu_conv_one dconv_eps_one dconv_congr_left dconv_congr_right)
open E213.Lib.Math.NumberTheory.MobiusFunction (mu)
open E213.Lib.Math.Combinatorics.Stirling (stirling2 stirling2_zero_above)
open E213.Lib.Math.Combinatorics.StirlingOrthogonality (s s_zero_above stirling_orthogonality_sum)
open E213.Lib.Math.Combinatorics.StirlingOrthogonality2 (stirling_orthogonality2_sum)

/-! ## §1 — the shared engine: triangular-matrix inversion

The incidence algebra of a locally finite poset: a lower-triangular unit matrix `M`
(the poset's zeta) has an inverse `S` (its Möbius/antipode), and the orthogonality
`S·M = δ` turns the transform `g = M·f` into `f = S·g`. The proof is one Fubini swap
(`sumZ_swap`) + the orthogonality collapse (`sumZ_delta_collapse`) — the same engine
both cuts run on. -/

/-- Lower-triangularity lets the inner transform range extend from `[0,k]` to `[0,n]`
    for `k ≤ n`: the added terms `i ∈ (k,n]` vanish (`M k i = 0` for `i > k`). -/
theorem sumZ_extend_tri (M : Nat → Nat → Int) (f : Nat → Int)
    (htri : ∀ k i, k < i → M k i = 0) :
    ∀ (k n : Nat), k ≤ n →
      sumZ (k + 1) (fun i => M k i * f i) = sumZ (n + 1) (fun i => M k i * f i) := by
  intro k n hk
  obtain ⟨d, hd⟩ := Nat.le.dest hk
  have hsplit : sumZ (n + 1) (fun i => M k i * f i)
      = sumZ (k + 1) (fun i => M k i * f i)
        + sumZ d (fun j => M k (k + 1 + j) * f (k + 1 + j)) := by
    rw [show n + 1 = (k + 1) + d from by rw [Nat.add_right_comm k 1 d, hd]]
    exact sumZ_add_range (k + 1) d (fun i => M k i * f i)
  have htail : sumZ d (fun j => M k (k + 1 + j) * f (k + 1 + j)) = 0 := by
    rw [sumZ_congr d _ (fun _ => (0 : Int))
          (fun j _ => by
            rw [htri k (k + 1 + j)
                  (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_right (k + 1) j))]
            exact E213.Meta.Int213.zero_mul _)]
    exact sumZ_const_zero d
  rw [hsplit, htail, Int.add_zero]

/-- ★★★ **Incidence-algebra inversion (the shared engine).**  For a lower-triangular
    unit incidence matrix `M` with antipode `S` satisfying the orthogonality
    `Σ_{k=0}^{n} S(n,k)·M(k,i) = δ(n,i)`, the transform `g(n) = Σ_{k=0}^{n} M(n,k)·f(k)`
    inverts to `f(n) = Σ_{k=0}^{n} S(n,k)·g(k)`.  One Fubini swap + one orthogonality
    collapse — the move every Möbius/antipode inversion compiles to. -/
theorem inversion_from_orthogonality
    (M S : Nat → Nat → Int)
    (htri : ∀ k i, k < i → M k i = 0)
    (hortho : ∀ n i, sumZ (n + 1) (fun k => S n k * M k i) = delta n i)
    (f g : Nat → Int) (hg : ∀ n, g n = sumZ (n + 1) (fun k => M n k * f k)) :
    ∀ n, f n = sumZ (n + 1) (fun k => S n k * g k) := by
  intro n
  have step1 : sumZ (n + 1) (fun k => S n k * g k)
      = sumZ (n + 1) (fun k => sumZ (n + 1) (fun i => S n k * (M k i * f i))) := by
    apply sumZ_congr
    intro k hk
    show S n k * g k = sumZ (n + 1) (fun i => S n k * (M k i * f i))
    rw [hg k, sumZ_extend_tri M f htri k n (Nat.le_of_lt_succ hk),
        sumZ_mul_left (S n k) (n + 1) (fun i => M k i * f i)]
  rw [step1, sumZ_swap (n + 1) (n + 1) (fun k i => S n k * (M k i * f i))]
  rw [sumZ_congr (n + 1)
        (fun i => sumZ (n + 1) (fun k => S n k * (M k i * f i)))
        (fun i => delta n i * f i)
        (fun i _ => by
          show sumZ (n + 1) (fun k => S n k * (M k i * f i)) = delta n i * f i
          rw [sumZ_congr (n + 1)
                (fun k => S n k * (M k i * f i))
                (fun k => f i * (S n k * M k i))
                (fun k _ => by
                  show S n k * (M k i * f i) = f i * (S n k * M k i)
                  generalize S n k = a
                  generalize M k i = c
                  generalize f i = d
                  ring_intZ)]
          rw [sumZ_mul_left (f i) (n + 1) (fun k => S n k * M k i), hortho n i]
          generalize f i = d
          generalize delta n i = e
          ring_intZ)]
  exact (sumZ_delta_collapse f n).symm

/-! ## §2 — additive cut: binomial inversion as the engine instance

The Pascal matrix `M(n,k) = C(n,k)` is lower-triangular unit (`C(k,i)=0` for `i>k`),
its antipode is the signed binomial `S = sb`, and the orthogonality `Σ_k sb(n,k)·C(k,i)
= δ(n,i)` is `binomial_orthogonality`.  So binomial inversion is `inversion_from_orthogonality`
on the poset `(ℕ,≤)`. -/

/-- ★★ **Binomial inversion via the shared engine** (additive cut).  Given the binomial
    transform `g(n) = Σ_{k≤n} C(n,k)·f(k)`, the antipode recovers
    `f(n) = Σ_{k≤n} (−1)^{n−k}C(n,k)·g(k)` — `inversion_from_orthogonality` with
    `M = C`, `S = sb`, orthogonality `binomial_orthogonality`. -/
theorem binomial_inversion_via_engine (f g : Nat → Int)
    (hg : ∀ n, g n = sumZ (n + 1) (fun k => (choose n k : Int) * f k)) :
    ∀ n, f n = sumZ (n + 1) (fun k => sb n k * g k) :=
  inversion_from_orthogonality
    (fun n k => (choose n k : Int)) sb
    (fun k i hki => by
      show (choose k i : Int) = 0
      rw [choose_eq_zero_of_lt k i hki]; rfl)
    (fun n i => binomial_orthogonality n i)
    f g hg

/-! ## §3 — multiplicative cut: Möbius inversion as the incidence inverse-element

In the Dirichlet algebra (poset `(ℕ,∣)`) the structure element is `1` (constant one,
the zeta), the antipode is `μ`, and `μ ∗ 1 = ε` (`mu_conv_one`).  Inversion is then the
pure inverse-element argument `f = ε∗f = (μ∗1)∗f = μ∗(1∗f) = μ∗g` — associativity
(`dirichlet_assoc`), unit (`dconv_eps_one`), antipode (`mu_conv_one`).  The *same*
incidence-algebra inverse, with the divisibility poset replacing `(ℕ,≤)`. -/

/-- `μ ∗ 1 = ε` at every index (the `n = 0` empty convolution gives `0 = ε 0` too). -/
theorem mu_conv_one_all : ∀ m, dconv mu (fun _ => (1 : Int)) m = eps m := by
  intro m
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0; rfl
  · exact mu_conv_one m hm

/-- ★★ **Möbius inversion via the incidence inverse-element** (multiplicative cut).
    Given the divisor-sum transform `g = 1 ∗ f` (`g(n) = Σ_{d∣n} f(n/d)`), the antipode
    recovers `f = μ ∗ g`.  The convolution-inverse argument `μ∗(1∗f) = (μ∗1)∗f = ε∗f =
    f`, dual to `binomial_inversion_via_engine` under the multiplicative cut. -/
theorem mobius_inversion_via_ring (f g : Nat → Int)
    (hg : ∀ m, g m = dconv (fun _ => (1 : Int)) f m) :
    ∀ n, 0 < n → f n = dconv mu g n := by
  intro n hn
  rw [dconv_congr_right mu g (dconv (fun _ => (1 : Int)) f) hg n,
      (dirichlet_assoc mu (fun _ => (1 : Int)) f n hn).symm,
      dconv_congr_left (dconv mu (fun _ => (1 : Int))) eps f mu_conv_one_all n,
      dconv_eps_one f n hn]

/-! ## §3.5 — the partition lattice: Stirling inversion as the third poset

The third classical poset (after the chain `(ℕ,≤)` and divisibility `(ℕ,∣)`) is the
**partition lattice** `Π_n`.  Its zeta is the Stirling number of the second kind
`stirling2` (lower-triangular: `stirling2 k i = 0` for `i > k`), its antipode the signed
Stirling number of the first kind `s`, and the orthogonality `Σ_k s(n,k)·stirling2(k,i)
= δ(n,i)` is `stirling_orthogonality`.  So Stirling inversion is the *same*
`inversion_from_orthogonality` engine on a third poset — and, the inverse pair being
two-sided (`stirling_orthogonality2`), both directions are instances. -/

/-- Bridge: `StirlingOrthogonality.sumZ` and the engine's `sumZ` are the same fold
    (identical definitions, distinct names). -/
private theorem stir_sumZ_eq (f : Nat → Int) :
    ∀ N, E213.Lib.Math.Combinatorics.StirlingOrthogonality.sumZ N f = sumZ N f
  | 0 => rfl
  | N + 1 => by
      show E213.Lib.Math.Combinatorics.StirlingOrthogonality.sumZ N f + f N = sumZ N f + f N
      rw [stir_sumZ_eq f N]

/-- Bridge: the two `delta`s coincide (identical definitions). -/
private theorem stir_delta_eq :
    ∀ n m, E213.Lib.Math.Combinatorics.StirlingOrthogonality.delta n m = delta n m
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | n + 1, m + 1 => by
      show E213.Lib.Math.Combinatorics.StirlingOrthogonality.delta n m = delta n m
      exact stir_delta_eq n m

/-- Stirling orthogonality `Σ_k s(n,k)·S₂(k,i) = δ(n,i)` in the engine's `sumZ`/`delta`. -/
private theorem stir_hortho (n i : Nat) :
    sumZ (n + 1) (fun k => s n k * (stirling2 k i : Int)) = delta n i := by
  rw [← stir_sumZ_eq (fun k => s n k * (stirling2 k i : Int)) (n + 1), ← stir_delta_eq n i]
  exact stirling_orthogonality_sum n i

/-- Dual Stirling orthogonality `Σ_k S₂(n,k)·s(k,i) = δ(n,i)` in the engine's `sumZ`/`delta`. -/
private theorem stir_hortho2 (n i : Nat) :
    sumZ (n + 1) (fun k => (stirling2 n k : Int) * s k i) = delta n i := by
  rw [← stir_sumZ_eq (fun k => (stirling2 n k : Int) * s k i) (n + 1), ← stir_delta_eq n i]
  exact stirling_orthogonality2_sum n i

/-- ★★ **Stirling inversion via the shared engine** (partition lattice, `stirling2 → s`).
    Given `g(n) = Σ_{k≤n} S₂(n,k)·f(k)`, the first-kind antipode recovers
    `f(n) = Σ_{k≤n} s(n,k)·g(k)` — `inversion_from_orthogonality` with `M = stirling2`,
    `S = s`, orthogonality `stirling_orthogonality`. -/
theorem stirling_inversion_via_engine (f g : Nat → Int)
    (hg : ∀ n, g n = sumZ (n + 1) (fun k => (stirling2 n k : Int) * f k)) :
    ∀ n, f n = sumZ (n + 1) (fun k => s n k * g k) :=
  inversion_from_orthogonality
    (fun n k => (stirling2 n k : Int)) s
    (fun k i hki => by
      show (stirling2 k i : Int) = 0
      rw [stirling2_zero_above hki]; rfl)
    (fun n i => stir_hortho n i)
    f g hg

/-- ★★ **Stirling inversion, the other direction** (`s → stirling2`).  Given
    `g(n) = Σ_{k≤n} s(n,k)·f(k)`, the second-kind antipode recovers
    `f(n) = Σ_{k≤n} S₂(n,k)·g(k)` — the same engine with the roles of the two Stirling
    matrices swapped (`stirling_orthogonality2`).  The two-sidedness of the
    Stirling pair is the partition lattice's antipode involution. -/
theorem stirling_inversion_via_engine_dual (f g : Nat → Int)
    (hg : ∀ n, g n = sumZ (n + 1) (fun k => s n k * f k)) :
    ∀ n, f n = sumZ (n + 1) (fun k => (stirling2 n k : Int) * g k) :=
  inversion_from_orthogonality
    s (fun n k => (stirling2 n k : Int))
    (fun k i hki => by
      show s k i = 0
      exact s_zero_above hki)
    (fun n i => stir_hortho2 n i)
    f g hg

/-! ## §4 — the capstone: one antipode, three posets -/

/-- ★★★ **Incidence inversion under the two cuts of ℕ.**  One proof object exhibiting
    binomial inversion (additive cut, Pascal poset `(ℕ,≤)`, antipode the signed
    binomial) and Möbius inversion (multiplicative cut, divisibility poset `(ℕ,∣)`,
    antipode `μ`) as the *same* incidence-algebra inverse — the antipode of a
    locally finite poset, the cut choosing the poset. -/
theorem incidence_inversion_two_cuts
    (f g : Nat → Int)
    (hg_add : ∀ n, g n = sumZ (n + 1) (fun k => (choose n k : Int) * f k))
    (f' g' : Nat → Int)
    (hg_mul : ∀ m, g' m = dconv (fun _ => (1 : Int)) f' m) :
    (∀ n, f n = sumZ (n + 1) (fun k => sb n k * g k))
    ∧ (∀ n, 0 < n → f' n = dconv mu g' n) :=
  ⟨binomial_inversion_via_engine f g hg_add, mobius_inversion_via_ring f' g' hg_mul⟩

/-- ★★★ **One engine, three triangular posets.**  The single law
    `inversion_from_orthogonality` inverts on three classical posets — the chain `(ℕ,≤)`
    (binomial, signed-binomial antipode), and the partition lattice `Π_n` in both
    directions (`stirling2 → s` and `s → stirling2`).  Each conjunct is a literal
    instance of the *same* engine; the shared structure is the engine, not a coincidence.
    (The divisibility poset `(ℕ,∣)` is the same antipode in the Dirichlet algebra,
    `mobius_inversion_via_ring`; see `incidence_inversion_two_cuts`.) -/
theorem incidence_inversion_three_posets
    (f₁ g₁ : Nat → Int)
    (h₁ : ∀ n, g₁ n = sumZ (n + 1) (fun k => (choose n k : Int) * f₁ k))
    (f₂ g₂ : Nat → Int)
    (h₂ : ∀ n, g₂ n = sumZ (n + 1) (fun k => (stirling2 n k : Int) * f₂ k))
    (f₃ g₃ : Nat → Int)
    (h₃ : ∀ n, g₃ n = sumZ (n + 1) (fun k => s n k * f₃ k)) :
    (∀ n, f₁ n = sumZ (n + 1) (fun k => sb n k * g₁ k))
    ∧ (∀ n, f₂ n = sumZ (n + 1) (fun k => s n k * g₂ k))
    ∧ (∀ n, f₃ n = sumZ (n + 1) (fun k => (stirling2 n k : Int) * g₃ k)) :=
  ⟨binomial_inversion_via_engine f₁ g₁ h₁,
   stirling_inversion_via_engine f₂ g₂ h₂,
   stirling_inversion_via_engine_dual f₃ g₃ h₃⟩

end E213.Lib.Math.IncidenceInversion
