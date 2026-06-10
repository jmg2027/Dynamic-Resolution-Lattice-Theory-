# Icosahedral — the A₅ structure of the residue self-reference map

The §5.6 self-reference Möbius map `M = [[c,1],[1,1]] = [[2,1],[1,1]]`
(`Lib/Math/Algebra/Mobius213`) is, simultaneously, an ℝ-matrix with golden
eigenvalues `φ², 1/φ²` **and** — reduced mod `d = 5` — an order-5 element of
`PSL(2,𝔽₅) ≅ A₅` (the icosahedral rotation group). This sub-tree builds that
identification and the `A₅` flavour-symmetry layer it opens, grounding the CKM
apex frontier (`ckm_rho_eta_apex` (frontier)) in established
`A₅` golden-ratio flavour symmetry (`SU(5)×A₅` models, arXiv:1410.2057,
1312.0215).

All theorems PURE (∅-axiom). 46 thms / 0 dirty (9 files).

## Files

| File | Content |
|---|---|
| `OrderFive.lean` | `M` mod 5 by genuine 𝔽₅-matrix mult; `M⁵≡−I`, order **exactly** 5 in `PSL(2,5)≅A₅` (5-fold icosahedral rotation); `d=5` double role (disc `M` = field 𝔽₅). |
| `A5Bridge.lean` | `\|A₅\|=60`; the order-5 element's 3-rep character is `φ`; **eigenvalue `φ² =` character `φ + 1`** = the Fibonacci recurrence on convergents (one golden ratio, two readings). |
| `A5Reps.lean` | `A₅` irrep dims (`Σdim²=60`), Clebsch–Gordan dims (incl. `5⊗5=25=d²`, the DRLT channel count as an `A₅` sum), golden character orthonormality `χ²(5A)+χ²(5B)=φ²+1/φ²=NS=trace M`. |
| `GoldenMixing.lean` | The established golden solar-angle template `sin²θ₁₂=1/(φ²+1)≈0.276` (Fibonacci-bracketed `8/29<·<5/18`), `tan²θ₁₂=1/φ²`, from the order-5 generator eigenvector. Lepton template; quark CKM-apex is the open extension. |
| `SpanAreas.lean` | Convergent span-areas `det(v_m,v_{m+k})=−F₂ₖ` (position-independent); apex span (gen 1↔3, `k=2`) = `F₄=NS`, the CP-area integer skeleton; 3-generation CP triangle = minimal unit area. |
| `A5ThreeRepPhase.lean` | CP-phase origin: 3-rep order-5 eigenvalues = 5th roots `{1,ζ,ζ⁴}` (complex ζ = phase source); Gauss sums `{1/φ,−φ}` = roots of `x²+x−1`; 2-rep/3-rep period cover ratio `10/5 = NT`. Complements `ApexCPMechanism`'s 2-rep `M⁵=−1`. |
| `CyclotomicFive.lean` | ★ Number-theory unification: the prime `d=5` via `ℚ(ζ₅)` gives BOTH the golden modulus (real subfield `ℚ(√5)=ℚ(φ)`, periods = roots of `x²+x−1`) AND the `C₄` phase (`Gal(ℚ(ζ₅)/ℚ)≅(ℤ/5)^×≅C₄`); bridge `5=(2+i)(2−i)` (splits `ℤ[i]`→90°) vs inert `ℤ[ω]` (excludes 60°). |
| `A5RealityNoCP.lean` | ★ Rigorous negative result: A₅ 3-rep is REAL (FS indicator `+1`, golden cancels `12(1−φ)+12φ=12`), `A₅⊂SO(3)` ⇒ CP-conserving (`J=0`); gCP quantizes `δ∈{0,90,180,270}°`, never golden. So `δ=π/φ²` is NOT an A₅ quantity — `φ` is the (real) angle, `δ` the (complex) phase, distinct. |
| `Capstone.lean` | Bundles the "M is an A₅ order-5 element carrying φ" identification + honest scope. |

## Open extension (frontier)

This **bridges** `M` to `A₅` and gives the golden-mixing *mechanism* (order-5
generator eigenvector → golden angle). It does **not** yet derive the quark CKM
CP-apex value `R_u = 1/φ²` from an explicit `A₅`-triplet generation assignment
with the CP phase — that is the next step (`ckm_rho_eta_apex.md`): build the
quark-sector `A₅` assignment and read off the apex, comparing the `SU(5)×A₅`
model.
