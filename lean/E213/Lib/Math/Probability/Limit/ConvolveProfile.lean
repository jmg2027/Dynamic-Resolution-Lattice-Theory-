import E213.Lib.Math.Probability.Limit.DyadicCompletion
import E213.Meta.Nat.PureNat

/-!
# Probability — convolution `⋆` on a discrete weight-**profile** (the CLT profile leg)

`ConvolveRescaleContraction` built the **rescale** leg of convolve-and-rescale as
exact dyadic halving on the centered statistic `Dy = Nat × Nat`, and
`DyadicCompletion` landed the Gaussian **center** as the contraction's fixed
point through the modulated engine (`gaussian_center_fixed_via_engine`).  The leg
flagged open in the `gaussian_clt` decomposition is the
**convolution operator on a full weight-profile** (not just its center): the tree
had only `ProbabilityCut = (num, den)` masses + the `joint` ×-character, no
density / weight-function type.

This file builds that operator honestly and ∅-axiom.

## The profile type and the convolution `⋆`

A **profile** is a finite discrete weight `f : List Nat` — `f[k]` = the mass at
integer position `k` (`probability.md`'s weight, made into a function object).
The discrete convolution

    (f ⋆ g)[k] = Σ_{i+j=k} f[i]·g[j]

is the weight-reading of "adding two independent variables" — the *additive twin*
of `Independence.joint`'s ×↦· character (`gaussian_clt.md` reading 1).  It is
defined by the standard one-row recursion

    conv (a :: f) g = addL (scale a g) (0 :: conv f g)

(`0 :: ·` is the position-shift `×x`), pure `Nat`, no real analysis.

## What this file proves (the finite generator: the moments)

The **preserved moments** the CLT calculus names as the *finite generator* of the
Gaussian residue, ∅-axiom:

1. **Total mass multiplies** — `mass (f ⋆ g) = mass f · mass g`
   (`mass_conv`).  Convolving two distributions of total mass `M, N` gives mass
   `M·N`; for probability profiles (`mass = D`) this is normalization preserved.
2. **First moment is additive** — `momentNum (f ⋆ g) = momentNum f · mass g +
   mass f · momentNum g` (`momentNum_conv`).  Dividing by the (multiplied)
   masses, the **mean of a sum is the sum of the means**: `μ(f⋆g) = μ(f) + μ(g)`
   — the additive `+`-character (`Expectation.discreteNum_append`'s twin) now
   carried by the convolution operator itself.  This is the rescale's *centering*
   invariant: the mean composes additively, so the standardization dial knows
   exactly what to subtract.

These are the convolution leg of "convolve-and-rescale": `⋆` composes the
weights and the moments compose linearly; the **rescale** (the contractive leg,
`ConvolveRescaleContraction.Φ`) then standardizes, and at the variance-fixed
standardized point the moment vector is `Φ`'s `q=+1` fixed point — already landed
in `DyadicCompletion`.

## The self-convolution doubling map `Φ_profile`

`Φ_profile f = conv f f` (self-convolution — the *doubling* step of the
convolve-and-rescale iteration, before standardization).  Its action on the
read-outs is closed-form: `mass (Φ_profile f) = (mass f)²` (`mass_Phi_profile`)
and `momentNum (Φ_profile f) = 2 · (momentNum f · mass f)` (`momentNum_Phi_profile`).
In mean terms `μ(Φ_profile f) = 2·μ(f)`: the mean doubles per step — exactly the
un-rescaled growth the `1/√2` rescale (`ConvolveRescaleContraction.Φ`) then
cancels, leaving the centered moment fixed
(`DyadicCompletion.gaussian_center_fixed_via_engine`).

## Honest residual (what real-analytic machinery the repo lacks)

The full statement "the Gaussian **density profile** is `Φ_profile`'s fixed
point" needs a *continuous* limiting density and a metric on densities under
which convolve-rescale contracts to it — i.e. a characteristic-function / Fourier
argument, or a real-valued density space with an `L¹`/`L∞` modulus.  The repo has
no continuous density type (only `Real213` cuts and these discrete profiles), so
the lattice profile cannot itself be the contraction carrier: convolution
*widens* a profile (variance adds) and a lattice profile cannot be rescaled by
`1/√2` and stay on the integer lattice.  The contraction therefore lives on the
**standardized moment vector**, where the rescale halves the centered deviation —
which is exactly the `Dy`-contraction already built and routed through the engine.
So:

* **Built here (∅-axiom):** a genuine discrete convolution `⋆` on profiles; mass
  multiplicativity; first-moment additivity (mean composes ⇒ centering invariant);
  the self-convolution doubling map `Φ_profile` and its closed-form moment action.
* **Routed through the engine (`DyadicCompletion`):** the standardized moment
  `(mean = 0)` is `Φ`'s `q=+1` fixed point —
  `gaussian_center_fixed_via_engine`.
* **Residual (needs real-analytic density space):** the *shape of the density
  between the lattice points* as a single fixed-point object.  The discrete
  profile + its preserved moments are the finite generator the calculus names;
  the continuous interpolant is the reached-by-none limit.

All zero-axiom.
-/

namespace E213.Lib.Math.Probability.Limit.ConvolveProfile

open E213.Meta.Nat.PureNat (add_mul)

/-! ## 0. A pure commutative-monoid rearrangement (finishes `momentNum_conv`) -/

/-- `a + ((b + c) + d) = (b + d) + (a + c)` — pure `Nat` `add`-AC, ∅-axiom. -/
theorem add_ac4 (a b c d : Nat) :
    a + ((b + c) + d) = (b + d) + (a + c) := by
  rw [Nat.add_assoc b c d]                       -- a + (b + (c + d))
  rw [← Nat.add_assoc a b (c + d)]               -- (a + b) + (c + d)
  rw [Nat.add_comm a b]                          -- (b + a) + (c + d)
  rw [Nat.add_assoc b a (c + d)]                 -- b + (a + (c + d))
  rw [← Nat.add_assoc a c d]                     -- b + ((a + c) + d)
  rw [Nat.add_comm (a + c) d]                    -- b + (d + (a + c))
  rw [← Nat.add_assoc b d (a + c)]               -- (b + d) + (a + c)

/-! ## 1. The profile type and its read-outs -/

/-- A **profile**: a finite discrete weight, `f[k]` = the mass at position `k`. -/
abbrev Profile : Type := List Nat

/-- **Total mass** `Σ_k f[k]` — the normalization (probability profiles have
    `mass = D`, the common denominator). -/
def mass : Profile → Nat
  | []      => 0
  | a :: f  => a + mass f

/-- **First-moment numerator** `Σ_k k·f[k]` — the mean is `momentNum / mass`.
    The head mass sits at position `0` (contributes `0`); the tail's masses all
    shift up by one position, contributing `momentNum f + mass f`. -/
def momentNum : Profile → Nat
  | []      => 0
  | _ :: f  => momentNum f + mass f

/-! ## 2. Pointwise list operations: scale and add -/

/-- Scale every mass by `c`. -/
def scale (c : Nat) : Profile → Profile
  | []      => []
  | a :: f  => (c * a) :: scale c f

/-- Pointwise sum of two profiles (the longer tail survives). -/
def addL : Profile → Profile → Profile
  | [],      g       => g
  | f,       []      => f
  | a :: f,  b :: g  => (a + b) :: addL f g

/-! ## 3. The discrete convolution `⋆`

`conv (a :: f) g = addL (scale a g) (0 :: conv f g)` — distribute the head mass
`a` (at position `0`) over `g`, then shift the convolution of the tail (whose
masses sit one position higher) right by one (`0 :: ·`).  `(f ⋆ g)[k] =
Σ_{i+j=k} f[i]·g[j]`. -/
def conv : Profile → Profile → Profile
  | [],      _  => []
  | a :: f,  g  => addL (scale a g) (0 :: conv f g)

/-- Discrete convolution of profiles (`gaussian_clt.md` reading 1). -/
infixl:70 " ⋆ " => conv

/-! ## 4. Mass is multiplicative under `⋆` (normalization preserved) -/

/-- `mass (scale c f) = c · mass f`. -/
theorem mass_scale (c : Nat) : ∀ f : Profile, mass (scale c f) = c * mass f
  | []     => by show 0 = c * 0; rw [Nat.mul_zero]
  | a :: f => by
      show (c * a) + mass (scale c f) = c * (a + mass f)
      rw [mass_scale c f, Nat.mul_add]

/-- `mass (addL f g) = mass f + mass g`. -/
theorem mass_addL : ∀ f g : Profile, mass (addL f g) = mass f + mass g
  | [],     g       => by
      show mass (addL [] g) = mass [] + mass g
      cases g with
      | nil => rfl
      | cons b g => show mass (b :: g) = 0 + mass (b :: g); rw [Nat.zero_add]
  | a :: f, []      => by show a + mass f = (a + mass f) + 0; rw [Nat.add_zero]
  | a :: f, b :: g  => by
      show (a + b) + mass (addL f g) = (a + mass f) + (b + mass g)
      rw [mass_addL f g]
      -- (a+b) + (mass f + mass g) = (a + mass f) + (b + mass g)
      rw [Nat.add_assoc a b (mass f + mass g),
        ← Nat.add_assoc b (mass f) (mass g),
        Nat.add_comm b (mass f),
        Nat.add_assoc (mass f) b (mass g),
        ← Nat.add_assoc a (mass f) (b + mass g)]

/-- `mass (0 :: f) = mass f`. -/
theorem mass_shift (f : Profile) : mass ((0 : Nat) :: f) = mass f := by
  show 0 + mass f = mass f; rw [Nat.zero_add]

/-- **★ Total mass multiplies under convolution** (∅-axiom): `mass (f ⋆ g) =
    mass f · mass g`.  For probability profiles (`mass = D`) this is
    normalization preserved by convolution — the first preserved moment. -/
theorem mass_conv : ∀ f g : Profile, mass (f ⋆ g) = mass f * mass g
  | [],     g => by show 0 = 0 * mass g; rw [Nat.zero_mul]
  | a :: f, g => by
      show mass (addL (scale a g) ((0 : Nat) :: (f ⋆ g))) = (a + mass f) * mass g
      rw [mass_addL (scale a g) ((0 : Nat) :: (f ⋆ g)),
        mass_scale a g, mass_shift (f ⋆ g), mass_conv f g,
        add_mul a (mass f) (mass g)]

/-! ## 5. First moment is additive under `⋆` (mean of a sum = sum of means) -/

/-- `momentNum (scale c f) = c · momentNum f`. -/
theorem momentNum_scale (c : Nat) : ∀ f : Profile,
    momentNum (scale c f) = c * momentNum f
  | []     => by show 0 = c * 0; rw [Nat.mul_zero]
  | a :: f => by
      show momentNum (scale c f) + mass (scale c f) = c * (momentNum f + mass f)
      rw [momentNum_scale c f, mass_scale c f, Nat.mul_add]

/-- `momentNum (addL f g) = momentNum f + momentNum g`. -/
theorem momentNum_addL : ∀ f g : Profile,
    momentNum (addL f g) = momentNum f + momentNum g
  | [],     g       => by
      show momentNum (addL [] g) = momentNum [] + momentNum g
      cases g with
      | nil => rfl
      | cons b g =>
          show momentNum (b :: g) = 0 + momentNum (b :: g); rw [Nat.zero_add]
  | a :: f, []      => by
      show momentNum f + mass f = (momentNum f + mass f) + 0; rw [Nat.add_zero]
  | a :: f, b :: g  => by
      show momentNum (addL f g) + mass (addL f g)
        = (momentNum f + mass f) + (momentNum g + mass g)
      rw [momentNum_addL f g, mass_addL f g]
      -- (mf + mg) + (Mf + Mg) = (mf + Mf) + (mg + Mg)
      rw [Nat.add_assoc (momentNum f) (momentNum g) (mass f + mass g),
        ← Nat.add_assoc (momentNum g) (mass f) (mass g),
        Nat.add_comm (momentNum g) (mass f),
        Nat.add_assoc (mass f) (momentNum g) (mass g),
        ← Nat.add_assoc (momentNum f) (mass f) (momentNum g + mass g)]

/-- `momentNum (0 :: f) = momentNum f + mass f` (shift right by one position). -/
theorem momentNum_shift (f : Profile) :
    momentNum ((0 : Nat) :: f) = momentNum f + mass f := rfl

/-- **★ First moment is additive under convolution** (∅-axiom):
    `momentNum (f ⋆ g) = momentNum f · mass g + mass f · momentNum g`.
    Dividing by the (multiplied) masses, the **mean of a sum is the sum of the
    means** `μ(f⋆g) = μ(f) + μ(g)` — the additive `+`-character carried by `⋆`,
    the rescale's centering invariant. -/
theorem momentNum_conv : ∀ f g : Profile,
    momentNum (f ⋆ g) = momentNum f * mass g + mass f * momentNum g
  | [],     g => by
      show (0 : Nat) = 0 * mass g + 0 * momentNum g
      rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero]
  | a :: f, g => by
      show momentNum (addL (scale a g) ((0 : Nat) :: (f ⋆ g)))
        = (momentNum f + mass f) * mass g + (a + mass f) * momentNum g
      rw [momentNum_addL (scale a g) ((0 : Nat) :: (f ⋆ g)),
        momentNum_scale a g, momentNum_shift (f ⋆ g),
        mass_conv f g, momentNum_conv f g,
        add_mul (momentNum f) (mass f) (mass g),
        add_mul a (mass f) (momentNum g)]
      -- LHS: a*m(g) + ((m(f)*M(g) + M(f)*m(g)) + M(f)*M(g))
      -- RHS: (m(f)*M(g) + M(f)*M(g)) + (a*m(g) + M(f)*m(g))
      -- = add_ac4 (a*m(g)) (m(f)*M(g)) (M(f)*m(g)) (M(f)*M(g))
      exact add_ac4 (a * momentNum g) (momentNum f * mass g)
        (mass f * momentNum g) (mass f * mass g)

/-! ## 6. The mean read-out and additivity of the mean -/

/-- The **mean** of a profile, as a `ProbabilityCut`-style pair
    `(momentNum f, mass f)` read `momentNum / mass`. -/
def profileMean (f : Profile) : Nat × Nat := (momentNum f, mass f)

/-- **Mean of a convolution = sum of means** (cross-multiplied form, ∅-axiom).
    With `μ(f) = m_f/M_f`, `μ(g) = m_g/M_g`, the convolution has mean
    `momentNum(f⋆g)/mass(f⋆g) = (m_f·M_g + M_f·m_g)/(M_f·M_g) = μ(f) + μ(g)`.
    Stated as the equality of numerators over the common denominator. -/
theorem profileMean_conv (f g : Profile) :
    (profileMean (f ⋆ g)).1 = (profileMean f).1 * (profileMean g).2
        + (profileMean f).2 * (profileMean g).1
    ∧ (profileMean (f ⋆ g)).2 = (profileMean f).2 * (profileMean g).2 :=
  ⟨momentNum_conv f g, mass_conv f g⟩

/-! ## 7. The self-convolution doubling map `Φ_profile` -/

/-- **`Φ_profile`** — the un-rescaled doubling step of convolve-and-rescale:
    self-convolution `f ↦ f ⋆ f`.  (The full `Φ` is `rescale ∘ Φ_profile`;
    the rescale's contractive core is `ConvolveRescaleContraction.Φ`.) -/
def Φ_profile (f : Profile) : Profile := f ⋆ f

/-- `mass (Φ_profile f) = (mass f)²` — total mass squares per doubling step. -/
theorem mass_Phi_profile (f : Profile) : mass (Φ_profile f) = mass f * mass f :=
  mass_conv f f

/-- `momentNum (Φ_profile f) = 2 · (momentNum f · mass f)` — the (un-normalized)
    first moment, so the **mean doubles** `μ(Φ_profile f) = 2·μ(f)`: the growth
    the `1/√2` rescale cancels.  `m·M + M·m = 2·(m·M)`. -/
theorem momentNum_Phi_profile (f : Profile) :
    momentNum (Φ_profile f) = 2 * (momentNum f * mass f) := by
  show momentNum (f ⋆ f) = 2 * (momentNum f * mass f)
  rw [momentNum_conv f f, Nat.two_mul, Nat.mul_comm (mass f) (momentNum f)]

/-! ## 8. Worked numeric witness (the fair-coin profile) -/

/-- The fair-coin one-step profile `[1, 1]` (mass `1` at `0`, mass `1` at `1`):
    mass `2`, first moment `1` (mean `1/2`). -/
theorem fair_profile_moments :
    mass [1, 1] = 2 ∧ momentNum [1, 1] = 1 := by
  refine ⟨?_, ?_⟩
  · show 1 + (1 + 0) = 2; rfl
  · show (momentNum [1] + mass [1]) = 1
    show ((momentNum ([] : Profile) + mass ([] : Profile)) + (1 + 0)) = 1
    rfl

/-- Self-convolving the fair-coin profile `[1,1] ⋆ [1,1] = [1, 2, 1]` (the
    binomial row `n=2`): mass `4 = 2²`, first moment `4 = 2·(1·2)` (mean `1`,
    doubled).  Both match `mass_Phi_profile` / `momentNum_Phi_profile`. -/
theorem fair_profile_doubled :
    Φ_profile [1, 1] = [1, 2, 1]
    ∧ mass (Φ_profile [1, 1]) = 4
    ∧ momentNum (Φ_profile [1, 1]) = 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · rw [mass_Phi_profile]; rfl
  · rw [momentNum_Phi_profile]; rfl

end E213.Lib.Math.Probability.Limit.ConvolveProfile
