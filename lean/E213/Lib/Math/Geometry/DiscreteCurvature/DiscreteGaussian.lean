import E213.Lib.Math.Combinatorics.Binomial
import E213.Lib.Math.Analysis.ODE.HeatEq.Conservation
import E213.Meta.Nat.PolyNatMTactic

/-!
# The discrete Gaussian heat kernel — `𝓦`-normalization + Li–Yau Harnack (∅-axiom)

The `(4πτ)^{−n/2}e^{−f}` **Gaussian normalization** of the `𝓦`-entropy and the **Li–Yau
differential Harnack** estimate, on the binomial heat kernel.
Both have an exact discrete core on the binomial heat
kernel, and this file establishes that core, `∅`-axiom.

**The kernel.**  The fundamental solution of the discrete heat equation on `ℤ` (numerator
form, stencil `(½,½)`) starting from the `δ`-measure is the **binomial kernel**
`u(t,x) = C(t,x)` (`binom t x`): the Pascal recursion *is* the heat step
(`heat_kernel_step`), and `u(0,·) = δ₀` (`heat_kernel_delta`).  De Moivre–Laplace makes it
the Gaussian `(4πτ)^{−1/2}e^{−x²/4τ}` in the continuum limit — *that* limit is not claimed
here; the discrete statements are exact.

**What is delivered:**

  1. `gaussian_normalization` — `Σ_x u(t,x) = 2^t`: the kernel's total mass is *exactly*
     the stencil normalization for **all** time, i.e. `u(t,·)/2^t` is a probability
     measure for every `t`.  This is precisely what the `(4πτ)^{−n/2}` prefactor of
     Perelman's `𝓦`-measure `(4πτ)^{−n/2}e^{−f}dV` enforces in the continuum
     (`∫(4πτ)^{−n/2}e^{−f} = 1`): the discrete `𝓦`-Gaussian normalization, an identity.
  2. `gaussian_mean` — `2·Σ_x x·u(t,x) = t·2^t`: the kernel's centre of mass drifts
     linearly (`⟨x⟩ = t/2`), the exact first moment (the `τ`-scaling of the Gaussian).
  3. `gaussian_li_yau` — **the discrete Li–Yau gradient estimate**: spatial
     log-concavity `u(t,x)·u(t,x+2) ≤ u(t,x+1)²` (`binom_log_concave`), the cleared,
     division-free form of `Δ log u ≤ 0` / the `|∇log u|²` Harnack quantity.  The
     `Real213`-division wall is sidestepped: the nonlinearity (`∇log u`) lives in the
     cross-multiplied products.
  4. `harnack_forward` — Harnack propagation: `u(t,x) ≤ u(t+1,x)` and
     `u(t,x) ≤ u(t+1,x+1)` — positivity propagates forward in time with constant `1`
     (numerator form), the integrated-Harnack shape `u(t,x) ≤ C·u(t+1,y)`.

**Honest boundary**: the continuum Li–Yau `Δlog u ≥ −n/2t` on a manifold with
`Ric ≥ 0` (and its coupling to Ricci flow, Hamilton's matrix Harnack) remains open; what
is closed is the exact kernel-level estimate the continuum statement discretizes to.
-/

namespace E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteGaussian

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Combinatorics.Binomial
  (binom_n_0 binom_n_1 binom_vanish binom_log_concave binom_le_binom_succ
   binom_le_binom_succ_succ binom_le_central)
open E213.Lib.Math.Analysis.ODE.HeatEq.Discrete
  (gridSum gridSum_succ gridSum_congr gridSum_add gridSum_head_shift gridSum_le
   gridSum_const gridSum_term_le)

/-! ## §1 — the kernel: `δ`-initial data, Pascal = heat step -/

/-- The discrete Gaussian heat kernel: `u(t,x) = C(t,x)` (numerator form; the
    normalized kernel is `u/2^t`). -/
def heatKernel (t x : Nat) : Nat := binom t x

/-- `u(0,·) = δ₀`: the kernel starts as the point measure. -/
theorem heat_kernel_delta : heatKernel 0 0 = 1 ∧ ∀ x, heatKernel 0 (x + 1) = 0 :=
  ⟨rfl, fun _ => rfl⟩

/-- **Pascal = heat step**: `u(t+1, x+1) = u(t,x) + u(t,x+1)` — the `(½,½)`-stencil
    heat evolution in numerator form (definitional). -/
theorem heat_kernel_step (t x : Nat) :
    heatKernel (t + 1) (x + 1) = heatKernel t x + heatKernel t (x + 1) := rfl

/-! ## §2 — the `𝓦`-Gaussian normalization: mass exactly `2^t` for all time -/

/-- ★★★★★ **The discrete Gaussian normalization**: `Σ_{x≤t} u(t,x) = 2^t` — the kernel's
    total mass equals the stencil normalization at **every** time, so the normalized
    kernel is a probability measure for all `t`.  The discrete content of Perelman's
    `(4πτ)^{−n/2}` prefactor (`∫(4πτ)^{−n/2}e^{−f}dV = 1` along the conjugate heat flow),
    here an exact `ℕ`-identity by induction on the Pascal recursion. -/
theorem gaussian_normalization : ∀ t : Nat,
    gridSum (t + 1) (fun x => heatKernel t x) = 2 ^ t
  | 0 => rfl
  | t + 1 => by
    have ihn : gridSum (t + 1) (fun x => binom t x) = 2 ^ t := gaussian_normalization t
    have hs : gridSum (t + 1) (fun x => binom (t + 1) (x + 1)) + binom (t + 1) 0
        = gridSum (t + 2) (fun x => binom (t + 1) x) :=
      gridSum_head_shift (t + 1) (fun x => binom (t + 1) x)
    have hsplit : gridSum (t + 1) (fun x => binom (t + 1) (x + 1))
        = gridSum (t + 1) (fun x => binom t x)
          + gridSum (t + 1) (fun x => binom t (x + 1)) := by
      rw [gridSum_congr (t + 1) (fun x => binom (t + 1) (x + 1))
            (fun x => binom t x + binom t (x + 1)) (fun x _ => rfl)]
      exact gridSum_add (t + 1) _ _
    have hs2 : gridSum (t + 1) (fun x => binom t (x + 1)) + binom t 0
        = gridSum (t + 2) (fun x => binom t x) :=
      gridSum_head_shift (t + 1) (fun x => binom t x)
    have htop : gridSum (t + 2) (fun x => binom t x)
        = gridSum (t + 1) (fun x => binom t x) + binom t (t + 1) :=
      gridSum_succ (t + 1) (fun x => binom t x)
    rw [binom_n_0] at hs2
    have hs2' : gridSum (t + 1) (fun x => binom t (x + 1)) + 1 = 2 ^ t := by
      rw [hs2, htop, binom_vanish t (t + 1) (Nat.lt_succ_self t), Nat.add_zero]
      exact ihn
    show gridSum (t + 2) (fun x => binom (t + 1) x) = 2 ^ (t + 1)
    rw [← hs, hsplit, ihn, binom_n_0, Nat.add_assoc, hs2', Nat.pow_succ]
    ring_nat

/-- ★★★ **The kernel's first moment**: `2·Σ_x x·u(t,x) = t·2^t`, i.e. the centre of mass
    is exactly `⟨x⟩ = t/2` for all time — the linear drift of the discrete Gaussian (its
    `τ`-scaling), again an exact identity. -/
theorem gaussian_mean : ∀ t : Nat,
    2 * gridSum (t + 1) (fun x => x * heatKernel t x) = t * 2 ^ t
  | 0 => rfl
  | t + 1 => by
    have hs : gridSum (t + 1) (fun x => (x + 1) * binom (t + 1) (x + 1))
          + 0 * binom (t + 1) 0
        = gridSum (t + 2) (fun x => x * binom (t + 1) x) :=
      gridSum_head_shift (t + 1) (fun x => x * binom (t + 1) x)
    have hsplit : gridSum (t + 1) (fun x => (x + 1) * binom (t + 1) (x + 1))
        = gridSum (t + 1) (fun x => x * binom t x + binom t x)
          + gridSum (t + 1) (fun x => (x + 1) * binom t (x + 1)) := by
      rw [gridSum_congr (t + 1) (fun x => (x + 1) * binom (t + 1) (x + 1))
            (fun x => (x * binom t x + binom t x) + (x + 1) * binom t (x + 1))
            (fun x _ => by
              show (x + 1) * (binom t x + binom t (x + 1))
                  = (x * binom t x + binom t x) + (x + 1) * binom t (x + 1)
              ring_nat)]
      exact gridSum_add (t + 1) _ _
    have hsplit2 : gridSum (t + 1) (fun x => x * binom t x + binom t x)
        = gridSum (t + 1) (fun x => x * binom t x)
          + gridSum (t + 1) (fun x => binom t x) :=
      gridSum_add (t + 1) _ _
    have h3 : gridSum (t + 1) (fun x => (x + 1) * binom t (x + 1))
        = gridSum (t + 1) (fun x => x * binom t x) := by
      have hs2 : gridSum (t + 1) (fun x => (x + 1) * binom t (x + 1)) + 0 * binom t 0
          = gridSum (t + 2) (fun x => x * binom t x) :=
        gridSum_head_shift (t + 1) (fun x => x * binom t x)
      have htop : gridSum (t + 2) (fun x => x * binom t x)
          = gridSum (t + 1) (fun x => x * binom t x) + (t + 1) * binom t (t + 1) :=
        gridSum_succ (t + 1) (fun x => x * binom t x)
      have hfull : gridSum (t + 1) (fun x => (x + 1) * binom t (x + 1)) + 0 * binom t 0
          = gridSum (t + 1) (fun x => x * binom t x) := by
        rw [hs2, htop, binom_vanish t (t + 1) (Nat.lt_succ_self t), Nat.mul_zero,
            Nat.add_zero]
      rw [← hfull, Nat.zero_mul]
      exact (Nat.add_zero _).symm
    have ih : 2 * gridSum (t + 1) (fun x => x * binom t x) = t * 2 ^ t := gaussian_mean t
    have hnorm : gridSum (t + 1) (fun x => binom t x) = 2 ^ t := gaussian_normalization t
    show 2 * gridSum (t + 2) (fun x => x * binom (t + 1) x) = (t + 1) * 2 ^ (t + 1)
    rw [← hs, hsplit, hsplit2, h3, hnorm, Nat.zero_mul, Nat.add_zero,
        show 2 * ((gridSum (t + 1) (fun x => x * binom t x) + 2 ^ t)
              + gridSum (t + 1) (fun x => x * binom t x))
          = 2 * gridSum (t + 1) (fun x => x * binom t x)
            + 2 * gridSum (t + 1) (fun x => x * binom t x) + 2 * 2 ^ t from by ring_nat,
        ih, Nat.pow_succ]
    ring_nat

/-! ## §3 — Li–Yau gradient estimate + Harnack propagation -/

/-- ★★★★★ **The discrete Li–Yau gradient estimate**: the heat kernel is log-concave in
    space, `u(t,x)·u(t,x+2) ≤ u(t,x+1)²` — the division-free cleared form of
    `Δ log u ≤ 0` (equivalently, the Li–Yau quantity `|∇log u|²` is controlled: the ratio
    `u(t,x+1)/u(t,x)` is monotone in `x`).  The `Real213`-division wall of the continuum
    Li–Yau is sidestepped by stating the estimate in cross-multiplied form; the proof is
    the absorption identity (`binom_log_concave`). -/
theorem gaussian_li_yau (t x : Nat) :
    heatKernel t x * heatKernel t (x + 2) ≤ heatKernel t (x + 1) * heatKernel t (x + 1) :=
  binom_log_concave t x

/-- ★★★ **Harnack propagation**: the kernel dominates its own past — `u(t,x) ≤ u(t+1,x)`
    and `u(t,x) ≤ u(t+1,x+1)` (numerator form).  The discrete integrated-Harnack shape
    `u(t,x) ≤ C·u(t+s,y)`: positivity spreads forward in time, with explicit constant. -/
theorem harnack_forward (t x : Nat) :
    heatKernel t x ≤ heatKernel (t + 1) x ∧ heatKernel t x ≤ heatKernel (t + 1) (x + 1) :=
  ⟨binom_le_binom_succ t x, binom_le_binom_succ_succ t x⟩

/-! ## §4 — no-local-collapsing: the kernel's central density is pinched

Perelman's no-local-collapsing rules out the cigar degeneration: along the flow, mass
cannot escape into a thin neck — volume density admits a lower bound at the curvature
scale.  Its discrete core on the kernel: the total mass `2^t` (`gaussian_normalization`)
lives on the support `{0,…,t}`, and **unimodality** (`binom_le_central`, from the same
absorption identity as the Li–Yau estimate) forces the centre to carry at least the
*average* density.  The kernel cannot flatten away (`no_local_collapsing`) nor blow up
past its mass (`kernel_le_mass`) — the two-sided density pinch. -/

/-- ★★★★★ **Discrete no-local-collapsing**: the kernel's central value dominates the
    average density — `2^{2n} ≤ (2n+1)·u(2n,n)` (cleared form of
    `u(2n,n) ≥ mass/support`).  Mass conservation + unimodality: the discrete reason the
    heat kernel cannot locally collapse, with the same absorption-identity engine as the
    Li–Yau gradient estimate (§3) — normalization + monotonicity ⟹ non-collapsing,
    Perelman's `𝓦` ⟹ κ-noncollapsing implication in kernel form. -/
theorem no_local_collapsing (n : Nat) :
    2 ^ (2 * n) ≤ (2 * n + 1) * binom (2 * n) n := by
  have hle : gridSum (2 * n + 1) (fun x => binom (2 * n) x)
      ≤ gridSum (2 * n + 1) (fun _ => binom (2 * n) n) :=
    gridSum_le (2 * n + 1) _ _ (fun k _ => binom_le_central n k)
  have hnorm : gridSum (2 * n + 1) (fun x => binom (2 * n) x) = 2 ^ (2 * n) :=
    gaussian_normalization (2 * n)
  rw [← hnorm]
  exact Nat.le_trans hle (Nat.le_of_eq (gridSum_const (2 * n + 1) (binom (2 * n) n)))

/-- **Non-concentration** (companion upper bound): no kernel value exceeds the total
    mass, `u(t,x) ≤ 2^t` (term ≤ sum, or vanishing off the support). -/
theorem kernel_le_mass (t x : Nat) : binom t x ≤ 2 ^ t := by
  rcases Nat.lt_or_ge x (t + 1) with h | h
  · rw [← gaussian_normalization t]
    exact gridSum_term_le (t + 1) (fun y => binom t y) x h
  · rw [binom_vanish t x h]
    exact Nat.zero_le _

/-- ★★★★ **The κ-noncollapsing pinch**: `mass/support ≤ central value ≤ mass`, i.e.
    `2^{2n} ≤ (2n+1)·u(2n,n)` and `u(2n,n) ≤ 2^{2n}` — the kernel's density at the
    centre is pinched within a factor `2n+1` of the mass: neither collapse (cigar) nor
    concentration (δ-relapse) happens along the discrete flow. -/
theorem kernel_density_pinch (n : Nat) :
    2 ^ (2 * n) ≤ (2 * n + 1) * binom (2 * n) n
    ∧ binom (2 * n) n ≤ 2 ^ (2 * n) :=
  ⟨no_local_collapsing n, kernel_le_mass (2 * n) n⟩

/-- ★★★★ **The discrete `𝓦`-Gaussian package**: `δ`-initial data + Pascal heat step +
    all-time mass normalization + Li–Yau log-concavity, in one bundle — the discrete
    core of the `(4πτ)^{−n/2}e^{−f}` Gaussian of Perelman's `𝓦`. -/
theorem w_gaussian_package (t x : Nat) :
    heatKernel 0 0 = 1
    ∧ heatKernel (t + 1) (x + 1) = heatKernel t x + heatKernel t (x + 1)
    ∧ gridSum (t + 1) (fun y => heatKernel t y) = 2 ^ t
    ∧ heatKernel t x * heatKernel t (x + 2)
        ≤ heatKernel t (x + 1) * heatKernel t (x + 1) :=
  ⟨rfl, rfl, gaussian_normalization t, gaussian_li_yau t x⟩

end E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteGaussian
