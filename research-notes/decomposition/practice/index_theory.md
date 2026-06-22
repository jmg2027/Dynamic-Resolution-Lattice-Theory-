# Decomposition: index theory / the Atiyah–Singer index theorem

*213-decomposition of "the Fredholm index `ind(D) = dim ker D − dim coker D`, the **analytic
index**, the **topological index** `∫_M ch(σ(D))·Td(M)`, **Atiyah–Singer** (analytic index =
topological index), the **McKean–Singer** heat-kernel formula `ind(D) = Σ_i (−1)^i = str e^{−tD²}`,
and the special cases Gauss–Bonnet (`D = d+d*`, `ind = χ`) and Riemann–Roch (`D = ∂̄`)", per
`../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants — the character arrow `×↦·`/`×↦+`
and the `q=±1` residue tag — + the q=±1 spine + the "two readings of one object coincide" collapse:
`det/tr=e_i`, the Lefschetz fixed-point=trace).*

This entry sits directly on three neighbors and consolidates them onto **one new datum**:
- `lefschetz_degree.md` (KEY) — the Lefschetz number `L(f) = Σ(−1)^i tr(f_*|H^i)` = the
  trace-character (`×↦+`, `tr=e₁`) alternating-summed down the fold-height with the `q=±1`
  orientation bit; `L(id) = χ`; the fixed-point theorem = the diagonal engine.
- `characteristic_classes.md` (JUST DONE) — `ch`/`Td` = the `×↦·`/`×↦+` character of the curvature
  spectrum landed in de Rham cohomology; `c_i = e_i(spectrum Ω)`; Gauss–Bonnet–Chern = the built
  `Σκ = 2χ` telescope.
- `homological_algebra.md` — `ker/im = ker/coker` = the residue (`Residue(L,C)`), tagged `q=±1`.

**The thesis under test (the NEW datum):** the index theorem is the calculus's **q=±1 alternating
count `ker − coker` (the analytic index) shown EQUAL to the `×↦·` character of the curvature (the
topological index)** — and *that equality* is the deepest instance of the corpus's recurring "two
readings of one object coincide" (det/tr=e_i; Lefschetz fixed-point=trace; the spectral split
dissolved into Vieta). Concretely:

- `ind(D) = dim ker D − dim coker D` = the **q=±1 alternating residue count** — the SAME ker/im=ker/coker
  residue `homological_algebra.md` reads (`object1_injective` faithful / `object1_not_surjective`
  surplus), now read with the **`q=±1` sign**: `ker D` is the `q=+1` pole (the part that closes,
  `converge`), `coker D` the `q=−1` pole (the obstruction, `escape`), and the index is their *signed
  difference* — a `multiplier` ∓1 weighting of the two residue poles (`ResidueTag`).
- McKean–Singer `ind(D) = Σ_i (−1)^i = str e^{−tD²}` = `lefschetz_degree.md`'s trace-weighted
  alternating sum **EXACTLY**: the index is a **Lefschetz number** — `L(id)` twisted by `D`, the
  Euler-characteristic-style alternating count `Σ(−1)^i tr` (`simplex_face_euler_zero`,
  `tr_eq_e1`). The supertrace `str` is the `(−1)^i`-graded trace = the README's `q=±1`-weighted
  fold-height read against the heat operator.
- `∫_M ch(σ(D))·Td(M)` = `characteristic_classes.md`'s `×↦·`/`×↦+` curvature character integrated
  (`ch` = the Chern character, the `×↦+` exp-twin of curvature; `det2_mul`/`vp_mul`).
- **Atiyah–Singer (analytic = topological)** = the deepest collapse: the q=±1 alternating count
  (analytic, `ker − coker`) EQUALS the `×↦·` character of the curvature (topological) — the SAME
  "two readings of one object are equal" as `det/tr=e_i` and Lefschetz fixed-point=trace.
- Special cases: Gauss–Bonnet (`D = d+d*`, `ind = χ`, the built `DiscreteGaussBonnet`),
  Riemann–Roch (`D = ∂̄`). **No new primitive.**

## The decomposition (C / Reading / Residue)

- **Construction `C`** — TWO constructions meeting at the diagonal, exactly `lefschetz_degree.md`'s:
  1. the **graded chain/cochain complex** (`homological_algebra.md`/`characteristic_classes.md`'s
     simplex nesting, `Cochain`/`delta`), carrying `C`'s two read-off axes — a **fold-height** (the
     degree `i`) and a **direction/orientation bit `q=±1`** (the `(−1)^i` sign);
  2. an **elliptic operator** `D : Γ(E⁺) → Γ(E⁻)` read as a *self-map shape* against the diagonal —
     `D` self-pointing the construction, the `Object1 : Raw → (Raw → Bool)` / `f : A → A → B` shape
     of `OneDiagonal.lean`. The operator's **symbol** `σ(D)` is the curvature-flavoured
     `Mat2`/`riemUp` data of `characteristic_classes.md` (a `List Mat2` / abstract-index tensor),
     NOT a new bundle object.

- **Reading `L_ind` (the q=±1 alternating residue count = the index)** — read `D` to its two residue
  strata and take their **signed difference**:
  - `ker D` = the part of the reading that **closes** — the `q=+1`/`converge` pole
    (`converge_residue_fixed`, the residue that reaches a fixed point); the solutions `D u = 0`.
  - `coker D` = the **obstruction** — the `q=−1`/`escape` pole (`escape_residue_outside`,
    `object1_not_surjective`); the surplus `D` cannot point, the directions `D` misses.
  - `ind(D) = dim ker − dim coker` = the **`q=±1`-weighted count** of one residue: `multiplier .converge·
    dim ker + multiplier .escape· dim coker` with `multiplier ∓1` (`multiplier_unimodular`). This is
    `homological_algebra.md`'s `ker/im=ker/coker` residue read with the **README `q=±1` tag as a
    signed weight** — the Euler-characteristic-style alternating count of the elliptic complex.
  This composes two readings the calculus already isolates: (a) the **trace-character**
  (`×↦+`, `tr=e₁`, `lefschetz_degree.md`) and (b) the **alternating-sign down the height**
  (`(−1)^i`, `simplex_face_euler_zero`, the `q=±1` direction bit) — so `L_ind` is `lefschetz_degree.md`'s
  `L_χ↓` read against `D` instead of a general self-map: the **Lefschetz number of the identity
  twisted by `D`**.

- **Reading `L_top` (the topological index = the `×↦·` curvature character integrated)** — read the
  symbol's curvature through `characteristic_classes.md`'s character: `∫_M ch(σ(D))·Td(M)`. `ch` is
  the `×↦+` additive character (`tr exp Ω`, the `vp_mul` exp-twin); `Td` is a further `×↦·`/`×↦+`
  invariant polynomial of the curvature (the `e_i`/power-sum bookkeeping). So `L_top` is the SAME
  bidirectional character arrow read on the symbol's curvature, **landed in cohomology and
  integrated** — `characteristic_classes.md`'s reading, not a new one.

- **Residue / the EQUALITY** — Atiyah–Singer is `L_ind = L_top`. In the calculus this is **not** a
  new residue; it is the corpus's recurring **"two readings of one object coincide"**: the analytic
  reading (the `q=±1` alternating `ker − coker` count) and the topological reading (the `×↦·`
  curvature character integrated) are two views of **one object** (the elliptic complex / its
  symbol's spectrum), forced equal — the SAME shape as `det/tr=e₁/e₂` (two Vieta readings of one
  spectrum, `det_tr_split_is_e1_e2`) and Lefschetz fixed-point=trace (`L(f)≠0 ⟹ ∃ fixed pt`, the
  diagonal). The McKean–Singer heat-kernel proof IS this collapse made a *deformation*: `str e^{−tD²}`
  is `t`-independent (it equals `ind D` at every `t`), so `t→0` (local, → the topological integrand)
  and `t→∞` (spectral, → `ker − coker`) give the same number — the resolution dial
  (`continuity.md`/`derivative.md`) read at two ends of one invariant, the `q=+1` "reached by none,
  narrowed by the modulus" pole.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   the elliptic operator D : Γ(E⁺)→Γ(E⁻)  =  a self-map shape against the diagonal       (OneDiagonal / Object1)
   ker D                                  =  the q=+1 / converge residue pole (closes)    (converge_residue_fixed)
   coker D                                =  the q=−1 / escape residue pole (obstruction) (escape_residue_outside, object1_not_surjective)
   ind(D) = dim ker − dim coker           =  ⟨ elliptic complex | L_ind = the q=±1-weighted alternating residue count ⟩
                                          =  homological_algebra.md's ker/coker residue, signed by multiplier ∓1
   McKean–Singer ind(D)=Σ(−1)ⁱ=str e^{−tD²} = lefschetz_degree.md's L(f)=Σ(−1)ⁱtr  EXACTLY  (Lefschetz of id twisted by D)
   the supertrace str                      =  the (−1)ⁱ-graded trace = q=±1 fold-height × tr=e₁     (simplex_face_euler_zero, tr_eq_e1)
   the topological index ∫ ch(σD)·Td(M)    =  ⟨ symbol curvature | L_top = the ×↦· / ×↦+ character integrated ⟩  (ch = characteristic_classes.md)
   ch(σD) = the Chern character            =  the ×↦+ additive character of the curvature  (vp_mul; det2_mul Whitney)
   Td(M)                                   =  a further e_i/power-sum invariant polynomial of curvature  (det_tr_split_is_e1_e2 GENERALIZED)
   ★ Atiyah–Singer: ind(D) = ∫ ch(σD)·Td(M) =  L_ind = L_top  =  TWO READINGS OF ONE OBJECT COINCIDE  (det/tr=e_i; Lefschetz fp=trace)
   heat-kernel t-independence (t→0 vs t→∞)  =  the resolution dial read at two ends of one invariant (q=+1, reached by none)
   Gauss–Bonnet  (D=d+d*, ind=χ)           =  the built Σκ = 2χ telescope                  (gauss_bonnet_Kmn, totalCurv_eq, simplex_face_euler_zero)
   Riemann–Roch  (D=∂̄, ind=∫ch·Td=deg+1−g) =  the same equality on the ∂̄-complex          (Real213-cut residue; predicted-not-built)
```

The single move: **index theory is not a new edifice** — it is the calculus's `q=±1` alternating
residue count (`ker − coker`, `homological_algebra.md`'s residue signed by the tag = McKean–Singer's
Lefschetz sum, `lefschetz_degree.md`) shown EQUAL to the `×↦·` curvature character integrated
(`characteristic_classes.md`), and that equality is the deepest instance of the corpus's "two readings
coincide".

## Re-seeing table (the unification)

| classical index-theory object | the calculus's reading | repo status |
|---|---|---|
| `ker D` (solutions) | the `q=+1`/converge residue pole (closes) | **BUILT** (`converge_residue_fixed`, `ResidueTag`) |
| `coker D` (obstructions) | the `q=−1`/escape residue pole (surplus) | **BUILT** (`escape_residue_outside`, `object1_not_surjective`) |
| ★ `ind(D) = dim ker − dim coker` | the `q=±1`-weighted alternating residue count (`multiplier ∓1`) | **BUILT** as the tag + the `±1` weight (`residue_tag_two_poles`, `multiplier_unimodular`); the named `index` object ABSENT |
| ★ McKean–Singer `ind = Σ(−1)ⁱ = str e^{−tD²}` | `lefschetz_degree.md`'s `L(f)=Σ(−1)ⁱtr` = Lefschetz of `id` twisted by `D` | **BUILT discretely** (`simplex_face_euler_zero` `L(id)=χ`, `tr_eq_e1`); the `str e^{−tD²}` operator ABSENT |
| the supertrace `str` | the `(−1)ⁱ`-graded trace = `q=±1` fold-height × `tr=e₁` | **BUILT** as the alternating sign + trace (`simplex_face_euler_zero`, `tr_eq_e1`) |
| topological index `∫ ch(σD)·Td(M)` | the `×↦·`/`×↦+` curvature character integrated | **BUILT at the matrix level** (`det2_mul`, `vp_mul`, `det_tr_split_is_e1_e2`); the integral ABSENT |
| `ch(σD)` (Chern character) | the `×↦+` additive curvature character | exp char **BUILT** (`vp_mul`); `tr exp Ω` on a bundle structural (per `characteristic_classes.md`) |
| `Td(M)` (Todd class) | a further `e_i`/power-sum invariant polynomial of curvature | `e₁,e₂` **BUILT** (`det_tr_split_is_e1_e2`); named `Td` ABSENT |
| ★ Atiyah–Singer `ind(D)=∫ch·Td` | `L_ind = L_top` = two readings of one object coincide | the **collapse is the datum**; certified at the matrix/discrete level, the welded smooth identity ABSENT |
| heat-kernel `t`-independence | the resolution dial read at two ends of one invariant (`q=+1`) | **BUILT** as the dial (`compose_modulus_eq`/`ResolutionShift` per neighbors); the heat operator ABSENT |
| Gauss–Bonnet `ind(d+d*)=χ` | the built `Σκ = 2χ` curvature–Euler telescope | **BUILT discretely** (`gauss_bonnet_Kmn`, `totalCurv_eq`, `simplex_face_euler_zero`) |
| Riemann–Roch `ind(∂̄)=∫ch·Td` | the same equality on the `∂̄`-complex | structural; smooth/`Real213`-cut residue, no named object |
| the named `D`/`Fredholm`/`AtiyahSinger`/`Todd`/`RiemannRoch`/`heatKernel`/`str` objects | the smooth elliptic-operator / `Real213`-cut residue | **ABSENT** (grep-confirmed; the located break) |

## Revelation (collapse + forcing + the q=±1 spine)

**★ Collapse (the NEW datum) — Atiyah–Singer IS the corpus's "two readings of one object coincide",
read at its deepest.** The README's capstone has two recurring equalities of *one* object's two
readings: `det/tr = e₁/e₂` (the two Vieta coefficients of one spectrum, `det_tr_split_is_e1_e2`) and
the Lefschetz fixed-point = trace (`L(f)≠0 ⟹ ∃ fixed pt`, the diagonal weighted by `tr`). **The index
theorem is the *third and deepest* such equality**: the **analytic index** (the `q=±1` alternating
`ker − coker` count — `homological_algebra.md`'s residue signed by the tag = McKean–Singer's Lefschetz
sum) and the **topological index** (the `×↦·`/`×↦+` curvature character integrated —
`characteristic_classes.md`'s `ch·Td`) are two readings of **one object** (the elliptic complex / its
symbol's curvature spectrum), forced equal. So `homological_algebra.md` (the `ker/coker` residue),
`lefschetz_degree.md` (the trace-weighted alternating sum, `L(id)=χ`), and `characteristic_classes.md`
(the `c_i=e_i` curvature character) **were index theory the whole time** — Atiyah–Singer is the single
theorem that says the residue-count reading and the character-integral reading of the elliptic complex
coincide. This is the new contribution beyond re-skinning the three neighbors: not "index = a residue"
(homological_algebra) nor "index = a Lefschetz sum" (lefschetz_degree) nor "the integrand = ch·Td"
(characteristic_classes) — but that **the residue-count reading EQUALS the character-integral reading**,
the same `det/tr=e_i` / Lefschetz=trace coincidence, now between *analysis and topology*.

**Forcing — the McKean–Singer collapse is the heat-kernel `t`-independence, i.e. the resolution dial.**
`str e^{−tD²} = ind(D)` for **all** `t` is *forced* because the nonzero eigenvalues of `D²` cancel in
pairs between `E⁺` and `E⁻` (the `q=±1` orientation bits cancelling pairwise — the SAME
`simplex_face_euler_zero` / `∂²=0` mechanism), leaving only the `t`-independent `dim ker − dim coker`.
Then `t→0` gives the local curvature integrand (the topological index) and `t→∞` gives the spectral
`ker − coker` (the analytic index): **one invariant read at two ends of the resolution dial**
(`continuity.md`/`derivative.md`'s resolution parameter), the `q=+1` "reached by none, narrowed by the
modulus" pole. So Atiyah–Singer's *proof* is the calculus's resolution dial; its *statement* is the
two-readings collapse.

**The q=±1 spine (`SYNTHESIS.md` §3) on the index.** The index is literally a `q=±1`-weighted count of
the residue's two poles: `ker D` = the `q=+1`/`converge` pole (`converge_residue_fixed`, the part that
closes), `coker D` = the `q=−1`/`escape` pole (`escape_residue_outside`, `object1_not_surjective`, the
surplus that cannot be pointed), and `ind = dim ker − dim coker` is their signed difference with
`multiplier ∓1` (`multiplier_unimodular`). The vanishing theorems (when `ind = 0`) are the `q=+1`
balanced case; the index obstruction (`ind ≠ 0` ⟹ no nowhere-zero solution / a forced zero) is the
`q=−1` escape — **the same "the diagonal cannot be dodged"** as Lefschetz/Brouwer
(`no_surjection_of_fixedpointfree`), now counted with a `tr` weight down the height. Gauss–Bonnet is
the spine's geometric pole made an integer identity: `ind(d+d*) = χ = Σ(−1)^i b_i` = the built
`Σκ = 2χ = 2(1−b₁)` telescope (`gauss_bonnet_Kmn`, `totalCurv_eq`), curvature (the `q=−1` loop
residue) integrated = topology (the `b₁` homology residue) — *one* `q=±1` residue read as curvature on
one side and as `χ`/`ker−coker` on the other. This is `characteristic_classes.md`'s Gauss–Bonnet–Chern
leg = the index theorem for `D = d+d*`, identical.

So index theory = (the analytic index = the `q=±1` alternating `ker − coker` residue count =
McKean–Singer's Lefschetz sum, `homological_algebra.md` + `lefschetz_degree.md`) **=** (the topological
index = the `×↦·` curvature character `∫ch·Td`, `characteristic_classes.md`), with Atiyah–Singer the
EQUALITY and Gauss–Bonnet (`ind = χ`) the built special case — **no new primitive**.

## VALIDATE verdict — **EXTEND** (decisive consolidation: Atiyah–Singer = the third "two readings coincide"; one PREDICTION leg; one located break)

No new primitive, no break in the interior. Index theory slots entirely into v7.1: `C` = the elliptic
complex (the graded simplex/cochain `C` of `homological_algebra.md`/`characteristic_classes.md`,
carrying fold-height + `q=±1` direction) read against `D` (the diagonal self-map shape of
`lefschetz_degree.md`); `L_ind` = the `q=±1`-weighted alternating `ker − coker` residue count =
McKean–Singer's Lefschetz sum; `L_top` = the `×↦·`/`×↦+` curvature character integrated; the
"Residue"/equality = the corpus's "two readings of one object coincide" (`det/tr=e_i`, Lefschetz
fixed-point=trace), now between the analytic and topological readings. It is a **decisive
consolidation**: the three neighbors are revealed as the analytic-side residue count
(`homological_algebra`), its trace-weighted alternating form (`lefschetz_degree`, `L(id)=χ`), and the
topological-side character integral (`characteristic_classes`) — Atiyah–Singer welds them.

- **PREDICTION leg (honest):** the calculus *predicts* the form of the full theorem —
  `ind = dim ker − dim coker` (the `q=±1`-signed residue count, forced by the tag),
  `ind = Σ(−1)^i tr` (forced as `lefschetz_degree.md`'s Lefschetz sum, `L(id)=χ`), the integrand
  `ch(σD)·Td(M)` (forced as `characteristic_classes.md`'s curvature character), and the EQUALITY
  `L_ind = L_top` (forced as the `det/tr=e_i` two-readings collapse). The discrete special case —
  Gauss–Bonnet `Σκ = 2χ` (`gauss_bonnet_Kmn`) and the alternating Euler count
  (`simplex_face_euler_zero`) — is **closed ∅-axiom**. The full smooth identity at general `D` is
  grounded by analogy to the closed discrete/`Mat2` case, not independently closed (the same boundary
  `characteristic_classes.md`/`de_rham.md` locate).

- **Located break (the `characteristic_classes.md`/`de_rham.md` spirit):** the **named smooth
  index-theory object** — the elliptic operator `D`, the Fredholm index, the symbol `σ(D)`, the Todd
  class `Td`, the heat kernel `e^{−tD²}`, the supertrace `str`, `AtiyahSinger`/`RiemannRoch` as named
  theorems, and the de Rham/integration machinery `∫_M ch·Td` — is ABSENT (grep-confirmed below),
  predicted-not-built. The discrete parallel theory (Gauss–Bonnet `Σκ=2χ`, the alternating Euler
  count, the `ker/coker` residue, the `tr=e₁` trace, the `c_i=e_i` character) is the worked instance;
  the smooth elliptic operator + its heat kernel + the de Rham integral is the `Real213`-cut /
  smooth-tensor residue — exactly the boundary `characteristic_classes.md` (no smooth bundle/curvature
  2-form), `de_rham.md` (no smooth `Ω^k(M)`/de Rham iso), and `lefschetz_degree.md` (no `f_*:H^i→H^i`
  / no named `L(f)`/`deg` bundle) already locate. **The same located break, not a new one.**

## Verified Lean anchors (file:line:theorem — all grep-confirmed on `lean/E213`; purity via `tools/scan_axioms.py`, run from repo root this session)

| Leg | Theorem (file : line : name) | Status |
|---|---|---|
| ★★ **`ind = dim ker − dim coker` = the `q=±1`-weighted residue count** (ker=converge, coker=escape; the `±1` weight) | `Lib/Math/Foundations/ResidueTag.lean:228 : residue_tag_two_poles`; `:86 : multiplier_unimodular`; `:133 : escape_residue_outside`; `:160 : converge_residue_fixed`; `:180 : golden_is_converge` | **PURE, scanned 55/0** ✓ |
| ★ **ker/coker = the residue** (self-cover faithful = ker injective; not total = coker surplus) | `Lens/Foundations/FlatOntologyClosure.lean:47 : object1_injective`; `:61 : object1_not_surjective`; `:69 : self_covering_closure` | **PURE, scanned 7/0** ✓ |
| ★ **the `coker`/index obstruction = the diagonal engine** (fixed-point-free ⟹ self-cover leaves residue) | `Lens/Foundations/OneDiagonal.lean:51 : no_surjection_of_fixedpointfree`; `:43 : lawvere_fixed_point`; `:61 : cantor_via_lawvere` | **PURE, scanned 11/0** ✓ |
| ★ **McKean–Singer `ind = Σ(−1)ⁱ` = `lefschetz_degree.md`'s `L(id)=χ` alternating count** | `Lib/Physics/Simplex/FaceTerms.lean:125 : simplex_face_euler_zero` (`Σ(−1)^k binom(5,k)=0=(1−1)^5`) | **PURE, scanned 10/0** ✓ |
| ★ **the supertrace summand = the `×↦+` trace-character `tr=e₁`; det/tr=e₁/e₂ = Td/ch's Vieta** | `…/Real213/Mat2/Mat2Spectrum.lean:115 : tr_eq_e1`; `:103 : det_eq_e2`; `:204 : det_tr_split_is_e1_e2`; `:167 : disc_eq_gap_squared`; `:186 : spectrum_roots` | **PURE, scanned 9/0** ✓ |
| ★ **topological index `∫ch·Td` = the `×↦·`/`×↦+` curvature character** (Chern char additive on `⊕`; det Whitney) | `…/Real213/Markov/SternBrocotMarkov.lean:104 : det2_mul` (`×↦·`); `Lib/Math/NumberTheory/PrimeValuation.lean:96 : vp_mul` (`×↦+`, the `ch` exp-twin) | det2_mul ∅-axiom ✓; `vp_mul` PURE (per `characteristic_classes.md` 7/0) |
| ★ **Gauss–Bonnet special case `ind(d+d*)=χ` = the built `Σκ=2χ` telescope** | `…/DiscreteCurvature/DiscreteGaussBonnet.lean:42 : gauss_bonnet_Kmn` (`totalVertexCurv=2·χ`); `:47 : euler_eq_one_sub_b1`; `:53 : totalCurv_eq` (`=2−2b₁`) | **PURE, scanned 12/0** ✓ |
| `ker/coker` residue mechanism = `ker δ/im δ` (the homological-algebra residue) | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 : reduced_betti_d4_contractible`; `:42 : kerSizeDelta`; `:47/:52 : kerSize_5_0/1` | **PURE, scanned 11/0** ✓ |
| naturality / two-readings-factor = the Lens-morphism 2-cell (per `characteristic_classes.md`) | `Lens/Compose/Morphism.lean:37 : view_factors_through_morphism` | ∅-axiom ✓ (per `characteristic_classes.md` 3/0) |
| degree/winding = the `×↦·` holonomy character (per `lefschetz_degree.md`) | `…/Real213/ModularGeometry/HolonomyLattice.lean:108 : holonomy_append`; `:136 : det_holonomy_eq_one`; `:313 : first_loop_is_the_fold` | ∅-axiom ✓ (per `lefschetz_degree.md` 26/0) |
| cross-frame | `lefschetz_degree.md` (`L(f)=Σ(−1)ⁱtr`, `L(id)=χ`, the diagonal), `characteristic_classes.md` (`ch`/`Td`=curvature char, `c_i=e_i`, Gauss–Bonnet–Chern), `homological_algebra.md` (`ker/coker`=the residue), `de_rham.md` (`H*_dR`, smooth gap), `hyperbolic_geometry.md` (Gauss–Bonnet built) | prior, ∅-axiom ✓ |

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root, this session):**
`ResidueTag` 55/0 · `FlatOntologyClosure` 7/0 · `OneDiagonal` 11/0 · `FaceTerms` 10/0 ·
`Mat2Spectrum` 9/0 · `DiscreteGaussBonnet` 12/0 · `BettiKernel` 11/0. All PURE, 0 DIRTY.

## Dropped / flagged (predicted-not-built — honest, grep-confirmed absent)

- **No named `Fredholm` / `AtiyahSinger` / `index_theorem` / `analyticIndex` / `topologicalIndex`
  object in `lean/E213`.** Grep (case-insensitive) for
  `Fredholm`/`Atiyah`/`Singer`/`McKean`/`index_theorem`/`indexTheorem`/`analyticIndex`/`topologicalIndex`/`FredholmIndex`
  returns **zero Lean declarations** (the only superficial token-match across the repo is the
  unrelated `canonicalTruthMap_iff_aCountOdd`; the bare word "index" matches list/Fin indices
  everywhere, no index-theory object). Flagged predicted-not-built, exactly as `lefschetz_degree.md`
  flags its absent `Lefschetz`/`degree` object.
- **No `Todd` / `RiemannRoch` / `ToddClass` / `Riemann_Roch` object.** Grep: zero declarations. `Td`
  is the `e_i`/power-sum invariant-polynomial reading (`det_tr_split_is_e1_e2`, grounded for `e₁,e₂`
  only — the `Mat2` 2×2 ceiling `characteristic_classes.md` flagged); the named `Td`/Riemann–Roch
  object is absent. Riemann–Roch (`D=∂̄`, `ind=deg+1−g`) is the same equality on the `∂̄`-complex,
  structural / `Real213`-cut, predicted-not-built.
- **No heat kernel `e^{−tD²}` / supertrace `str` / elliptic operator `D` object.** Grep: zero
  `heat_kernel`/`heatKernel`/`supertrace`/`ellipticOperator`/`Dirac` index-theory declarations. The
  *summands* are built (`simplex_face_euler_zero` the `(−1)^i`, `tr_eq_e1` the trace), and the
  `t`-independence is the resolution dial (per neighbors); the `str e^{−tD²}` operator assembling them
  is absent — the McKean–Singer twin of `lefschetz_degree.md`'s missing `L(f)` bundle.
- **No `ker D`/`coker D` of a *named elliptic `D`*.** The residue mechanism `ker δ/im δ`
  (`BettiKernel`, `kerSizeDelta`) and the abstract self-cover ker/coker (`object1_injective`/
  `object1_not_surjective`) are built and PURE; there is no functorial `D : Γ(E⁺)→Γ(E⁻)` whose ker
  and coker are taken. This is the precise missing leg — the index twin of
  `homological_algebra.md`'s missing graded `Ext^n` bundle and `lefschetz_degree.md`'s missing
  `f_*:H^i→H^i`.
- **The smooth `∫_M ch(σD)·Td(M)` with the de Rham iso** — the `2πi` normalization, the smooth
  curvature 2-form `Ω∈Ω²(M;End E)`, the de Rham comparison `H*_dR≅H*_sing(·;ℂ)` that makes the index
  an *integer/topological* invariant — is the `Real213`-cut / smooth-manifold residue, the SAME
  boundary `characteristic_classes.md` (no smooth bundle) and `de_rham.md` (no smooth `Ω^k(M)`, no de
  Rham iso) locate. Only the discrete `Σκ=2χ` (`gauss_bonnet_Kmn`, integer-valued) and the alternating
  Euler count (`simplex_face_euler_zero`) are built. Cited scope-honest.
- **Verified buildable witness (no new claim asserted):** the load-bearing collapse is already a set
  of `decide`/`ring_intZ` theorems — Gauss–Bonnet `gauss_bonnet_Kmn`/`totalCurv_eq` (`ind(d+d*)=χ=2−2b₁`),
  the alternating Euler count `simplex_face_euler_zero` (`L(id)=χ`, the McKean–Singer sum's discrete
  form), the det/tr=e₁/e₂ Vieta (`det_tr_split_is_e1_e2`, the `ch`/`Td` curvature character), and the
  `q=±1` residue poles (`residue_tag_two_poles`, `multiplier_unimodular`, the signed `ker−coker`
  count) — all scanned PURE this session. A clean additional witness would be a `Mat2`/graph-level
  "signed pole count = Euler readout" — i.e. wiring `multiplier .converge·(dim ker) + multiplier
  .escape·(dim coker)` to `eulerChar`/`simplex_face_euler_zero` as one `decide` lemma; no new
  count-inequality is proposed beyond the grep-confirmed, scanned-PURE anchors above.
