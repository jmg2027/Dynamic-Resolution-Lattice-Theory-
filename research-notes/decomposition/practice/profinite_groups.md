# Decomposition: profinite groups / inverse limits (G = lim G_i, ℤ_p = lim ℤ/pⁿ, ℤ̂ = lim ℤ/n, the absolute Galois group, the Krull topology, profinite = Stone space of the finite-quotient lattice)

*A FRESH, deep decomposition per `../README.md` (model v7.1) and `SYNTHESIS.md`'s two invariants (the
character arrow `×↦·`/`×↦+`, the `q=±1` residue tag, read across the resolution axis with `base`). It sits
at the join of four neighbors: `padic.md` (KEY — ℤ_p = lim ℤ/pⁿ, the `base`=p resolution tower),
`iwasawa_theory.md` (JUST DONE — the ℤ_p-tower as `CompletionTower`, the level grades adding),
`stone_duality.md` (JUST DONE — profinite = Stone space, the calibrated ultrafilter/LLPO boundary),
`galois_cohomology.md`/`class_field_theory.md` (the Galois group, the bottom rung), and
`continued_fractions.md` (the modulus = the inverse-limit approximant). The thesis under TEST, not re-skin:*

> **A profinite group is the calculus's resolution-tower INVERSE LIMIT — the `CompletionTower`/`iProdLens`
> meet of finite groups, the limit = the modulus of finite approximations (reached-by-none), with the
> profinite=Stone tie placing it on the SAME calibrated ultrafilter/LLPO boundary `stone_duality.md`
> located.** Four legs:
> 1. **G = lim G_i, ℤ_p = lim ℤ/pⁿ** = `padic.md`'s p-adic resolution tower — each finite quotient G/N a
>    finite resolution, the inverse limit the modulus/approximant sequence. The SAME `CompletionTower`
>    Iwasawa used (completion = inverse limit); the level grades ADD (`IsResolutionShift_compose`).
> 2. **The inverse-limit universal property** (lim factors through every finite stage) = the **meet of a
>    Lens-family**'s greatest-lower-bound universal property (`iProdLens_is_greatest_pw`) — the modulus's
>    defining property, *built* ∅-axiom.
> 3. **profinite = compact totally-disconnected = the Stone space of the finite-quotient lattice** = the
>    `stone_duality.md` tie: the finite quotients ∅-axiom (Boolean/`decide` side), the inverse LIMIT as a
>    completed point on the Stone-space/ultrafilter side = the **calibrated LLPO boundary**.
> 4. **The absolute Galois group Gal(K̄/K) = lim Gal(L/K)** = `galois_cohomology.md`'s G taken to the
>    profinite limit; the bottom rung Gal(ℚ(ζ₅)/ℚ)≅C₄ is built (`galois_group_is_C4`).

**Headline, stated up front so the rest is honest.** This is a **PREDICTION + a genuine grounded surprise +
a located boundary**, and the surprise is large: unlike `iwasawa_theory.md` (where the *named* objects were
all absent), the repo **already builds a profinite inverse limit** — the abelian/ℤ̂ case — as two ∅-axiom
files written exactly to this thesis. `ProfiniteSeq.lean` (9/0) constructs the profinite ℤ̂ = lim ℤ/m limit
of the factorial sequence (`factorial_seq_familyCauchy`, `factorial_seq_limit_all_zero` = the profinite
zero), `GenericFamily.lean` (10/0) **explicitly unifies profinite ↔ archimedean as two Lens-family
choices**, `OdometerValue.lean` (16/0) builds ℤ₂ = lim ℤ/2ᵏ quantitatively (`bval_odo` = the profinite
successor `+1 mod 2ᵏ`, `odo_no_fixpoint`), and the inverse-limit **universal property** is the built meet of
a Lens-family (`iProdLens`/`iProdLens_is_greatest_pw`, IndexedJoin). What is ABSENT is the *non-abelian
group* structure on the limit (a `ProfiniteGroup` type, the Krull topology, the absolute Galois group, the
named `inverseLimit`) — grep-confirmed zero declarations. So: **PREDICTION on the group leg, genuinely BUILT
on the abelian inverse-limit + universal-property legs (the surprise), located boundary at the Stone/ultra-
filter side (calibrated at LLPO, `stone_duality.md`).**

## The decomposition (C / Reading / Residue)

- **Construction `C` — the inverse system of finite quotients, which is `padic.md`'s approximant-sequence-
  with-modulus read as a TOWER of finite groups.** A profinite group `G = lim_i G_i` is given by an inverse
  system `{G_i, φ_{ji}: G_j ↠ G_i}` of *finite* groups; ℤ_p = lim ℤ/pⁿ, ℤ̂ = lim_m ℤ/m, Gal(K̄/K) = lim_L
  Gal(L/K). The construction `C` is the *same* shape `padic.md`/`iwasawa_theory.md` use: a refinement
  sequence whose finite stages stabilize, plus a modulus. Each finite quotient G/N is one finite resolution
  (the count-Lens read mod N); the system is the resolution *iterated*. The repo builds exactly this `C` at
  the abelian level: the factorial sequence `xs` with `leaves(xs n) = factorial(n+1)` is family-Cauchy
  w.r.t. the family `{leavesModNat m : m ≥ 2}` (`factorial_seq_cauchy`), and its limit class is "0 mod m for
  every m" = the profinite zero of ℤ̂ (`factorial_seq_limit_zero`/`factorial_seq_limit_all_zero`). The
  finite stages here are the `leavesModNat m` readings — the count-Lens at resolution `m` — and the inverse
  system is the family. The quantitative ℤ₂ instance is `OdometerValue`: `bval k f` reads the first `k` bits
  (= the ℤ/2ᵏ truncation), `bval_odo` proves the odometer `odo` is `+1 mod 2ᵏ` on every truncation (the
  profinite successor), pinning the escape space as `ℤ₂ = lim ℤ/2ᵏ`. So `C` = the inverse system of finite
  count-Lens readings; the cyclotomic ℤ_p-tower (`padic.md`'s `base`=p) and ℤ̂ (the `base`=all-m family) are
  two fillings of the resolution `base` slot — the SAME `CompletionTower` (completion = inverse limit) Iwasawa
  ascended, where `tower_is_single_inner` proves the tower returns home with the modulus the only ascending
  datum and `IsResolutionShift_compose` proves the level grades add `(ℕ,+)`.

- **Reading `L_lim` — the inverse-limit / meet-of-the-finite-quotient-family reading. This is the leg the
  repo builds, and its universal property is the modulus's defining property.** The inverse limit reads the
  whole inverse system at once: a point of `lim G_i` is a *compatible thread* `(g_i)_i` agreeing under the
  transition maps. In the calculus this is the **meet of the Lens-family** `{(G_i-reading)}` — the indexed
  product Lens `iProdLens F` (IndexedJoin.lean:97), whose codomain is the dependent thread space
  `(i:ι) → (F i).1` and whose view at index `i` is exactly the `i`-th finite reading
  (`iProdLens_view`, :106). The inverse-limit **universal property** — "lim G_i is the terminal object
  factoring through every finite stage; any compatible cone factors uniquely" — is the **greatest-lower-bound
  property of the meet**: `iProdLens_refines_each` (:149, the limit projects onto each G_i) is the cone, and
  `iProdLens_is_greatest_pw` (:168, any `L` refining all `(F i).2` factors through `iProdLens F` at every
  index) is the universal/terminal half. This is the SAME "factors through every finite stage" the modulus
  has by `continued_fractions.md`'s doctrine — the limit is the modulus of finite approximations, defined by
  its threads, never held as a finite object. The family-Cauchy + limit-assignment machinery
  (`FamilyCauchy`, :105; `LimitAssignment`, :110; `LimitAssignment.limit`, :115;
  `pointwise_limit_match`, :124) is the inverse-limit *as the limit of the family-reading*, and the limit
  thread agrees pointwise with `iProdLens`'s view — the literal "the inverse limit IS the meet of the finite
  readings" identification, ∅-axiom.

- **Residue, tagged `q=±1` (`ResidueTag.lean`) — the completed thread, reached by no finite stage; and the
  Stone/ultrafilter reification on the calibrated boundary.**
  - **The completion residue (`q=+1` converge).** A point of `lim G_i` is reached by no finite quotient,
    only narrowed to by deeper threads — the `padic.md`/`CompletionTower` reached-by-none completion limit,
    the `q=+1` converging modulus-residue (the same modulated completion as `golden_is_converge`). The
    profinite zero `factorial_seq_limit_all_zero` is a concrete inhabited thread (the all-zero thread is the
    `q=+1` fixed point — the constant compatible thread); `odo_no_fixpoint` is the `q=−1` reminder that the
    successor `+1` never fixes a point (the act of pointing always changes a bit).
  - **The Stone/ultrafilter reification (`q=±1`, on the calibrated boundary).** `stone_duality.md`: a
    profinite group IS the Stone space of its lattice of finite-index (open normal) subgroups —
    profinite = compact totally-disconnected = a Stone space, the clopen sets the finite-index cosets. So the
    *individual finite quotients* are the `decide`/`Bool` Boolean side (∅-axiom: each G/N is a finite count,
    `leavesModNat m`), and the *inverse limit as a topological space whose points are reconstructed from all
    finite quotients at once* is the points-from-readings reconstruction at the maximal index — the SAME
    calibrated ultrafilter/LLPO boundary `stone_duality.md` located. The general (non-abelian, uncountable)
    profinite group's compactness — every profinite group is compact, equivalently the Tychonoff/Stone-space
    property — is the BPI/LLPO-strength totalization (`comparability_imp_llpo`→`llpo_of_realDichotomy`), no
    ∅-axiom witness in full generality. The residue's `q=±1` tag: faithful where the finite quotients
    determine the thread (`object1_injective`-style), un-pointable where the completion diagonalizes out
    (`object1_not_surjective`).

## Re-seeing — ⟨C | L_lim⟩ ⊕ Residue

```
   inverse system {G_i, φ_ji}        =  ⟨ approximant-with-modulus | L_res(base) ⟩ as a tower of finite groups   (padic.md's C, iterated)
   ℤ_p = lim ℤ/pⁿ                    =  the p-adic resolution tower (base=p)                                      (padic ZpSeq; CompletionTower)
   ℤ̂ = lim_m ℤ/m                     =  the count-Lens family {leavesModNat m} inverse limit                      (ProfiniteSeq, factorial_seq_familyCauchy, BUILT 9/0)  ★ SURPRISE
   ℤ₂ = lim ℤ/2ᵏ (quantitative)      =  the odometer +1 mod 2ᵏ on every truncation                                (OdometerValue.bval_odo, BUILT 16/0)  ★ SURPRISE
   a point of lim G_i (a thread)     =  a compatible thread in the meet of the finite-quotient family             (iProdLens.view; LimitAssignment.limit)
   inverse-limit universal property  =  the MEET's greatest-lower-bound universal property                        (iProdLens_refines_each + iProdLens_is_greatest_pw, BUILT 8/0)  ★ SURPRISE
   "factors through every finite stage" = the modulus's defining property                                          (continued_fractions doctrine; iProdLens_is_greatest_pw)
   completion = inverse limit        =  CompletionTower (group thresholds, group the groupings; returns home)      (tower_is_single_inner, rfl; 7/0)
   level grades ADD up the tower     =  (ℕ,+)-graded resolution count                                              (IsResolutionShift_compose, 17/0)
   profinite ↔ archimedean           =  two Lens-FAMILY choices, same limit mechanism                              (GenericFamily, BUILT 10/0)  ★ the unification, explicit
   profinite = compact tot.-disc.    =  the Stone space of the finite-quotient lattice                            (stone_duality.md; general case = LLPO/BPI boundary)
   the completed point               =  reached-by-none completion residue, q=+1 converge                          (ResidueTag golden_is_converge; CompletionTower)
   profinite zero (all-0 thread)     =  the q=+1 fixed-point thread, inhabited                                     (factorial_seq_limit_all_zero, BUILT)
   the +1 fixes no point             =  q=−1 escape reminder (pointing always changes a bit)                       (odo_no_fixpoint, BUILT)
   absolute Galois Gal(K̄/K)=lim Gal  =  galois_cohomology's G to the profinite limit                              (galois_group_is_C4 = bottom rung; ℤ_p-/Gal-tower OBJECT ABSENT)
   Krull topology                    =  the resolution dial (open ⟺ finite-index ⟺ a finite-stage fibre)          (stone_duality clopen↔element; named Krull OBJECT ABSENT)
   ProfiniteGroup as a type          =  the meet's codomain with a group law                                       (iProdLens codomain BUILT; the GROUP law on the limit ABSENT)
```

| classical profinite object | the calculus's reading | repo status |
|---|---|---|
| ℤ̂ = lim ℤ/m (the inverse limit of finite cyclic groups) | the count-Lens family `{leavesModNat m}` inverse limit | **BUILT** (`ProfiniteSeq`, 9/0 — profinite ℤ̂ zero), the surprise |
| ℤ_p = lim ℤ/pⁿ, ℤ₂ = lim ℤ/2ᵏ | the `base`=p resolution tower; the odometer `+1 mod 2ᵏ` | **BUILT** (`padic` ZpSeq; `OdometerValue.bval_odo`, 16/0) |
| inverse limit `lim G_i` (the object) | the meet of the finite-quotient Lens-family (`iProdLens`) | the meet + its universal property **BUILT** (`iProdLens_is_greatest_pw`, 8/0); the GROUP law on it **ABSENT** |
| inverse-limit universal property | the meet's greatest-lower-bound (terminal cone) | **BUILT** (`iProdLens_refines_each` + `iProdLens_is_greatest_pw`) |
| profinite = compact totally-disconnected = Stone space | `stone_duality.md`'s finite quotients (Boolean) + the limit (ultrafilter) | finite side **PURE**; full compactness = **LLPO/BPI boundary** (`comparability_imp_llpo`) |
| completion = inverse limit | `CompletionTower` (returns home, modulus ascends) | **BUILT** (`tower_is_single_inner`, 7/0; `IsResolutionShift_compose`, 17/0) |
| Gal(K̄/K) = lim Gal(L/K) (the absolute Galois group) | `galois_cohomology`'s G to the profinite limit | bottom rung **BUILT** (`galois_group_is_C4`, 4/0); the infinite Galois-tower OBJECT **ABSENT** |
| the Krull topology | the resolution dial: open ⟺ finite-index ⟺ a finite-stage fibre | clopen↔element conceptual (`stone_duality`); named `Krull` OBJECT **ABSENT** |
| `ProfiniteGroup` / `inverseLimit` / `absoluteGalois` as named types | — | **ABSENT** (grep-confirmed zero declarations) |

## ★ The new datum (not in padic.md / iwasawa_theory.md / stone_duality.md)

`padic.md` gave one completion (ℚ_p, `base`=p, at one level). `iwasawa_theory.md` ascended it into a tower
but found every *named* Iwasawa object absent. `stone_duality.md` located the ultrafilter boundary on the
Boolean algebra's spectrum. The NEW datum here is **three findings the neighbors did not touch**:

1. **The inverse limit is the MEET of the finite-quotient Lens-family, and its universal property is the
   meet's greatest-lower-bound — BUILT ∅-axiom.** `iProdLens` (IndexedJoin:97) is the inverse-limit object
   (the thread space), `iProdLens_refines_each` (:149) the projection cone, `iProdLens_is_greatest_pw` (:168)
   the terminal/universal half. The "lim factors through every finite stage" is *literally* the meet's GLB
   property. This is the inverse-limit universal property as a built theorem, which neither `padic.md` nor
   `iwasawa_theory.md` exhibited (they read off single completions / the tower shape; here it is the *limit
   of a family* with its universal property).

2. **The abelian profinite group ℤ̂ is genuinely BUILT — `ProfiniteSeq` constructs lim ℤ/m as a family-Cauchy
   limit.** The factorial sequence is family-Cauchy w.r.t. `{leavesModNat m}` and its limit is the profinite
   zero "0 mod m for all m" (`factorial_seq_limit_all_zero`, 9/0). `GenericFamily` (10/0) then proves
   profinite and archimedean are *the same abstraction* — two `(Lens, post-processing)` family choices
   (`profinite_factorial_is_GFCauchy`, `orderCauchy_is_GFCauchy`, both instances of `GFCauchy`). This is the
   thesis's "profinite=resolution-tower inverse limit" realized as a built ∅-axiom object for the abelian
   case — a stronger grounding than predicted.

3. **The profinite=Stone tie places the limit on the SAME calibrated LLPO boundary `stone_duality.md`
   located — and the boundary bites precisely at the GROUP law on the uncountable limit.** The finite
   quotients are the `decide`/`Bool` Boolean side (PURE), the inverse limit as a compact Stone space is the
   ultrafilter/LLPO side. The abelian/countable case dodges the wall (built via family-Cauchy over a
   countable index); the general non-abelian profinite group's compactness is the BPI-strength totalization
   — `comparability_imp_llpo`→`llpo_of_realDichotomy` (31/0), the same omniscience ledger. So the boundary is
   calibrated, not posited: the countable abelian inverse limit is built; the uncountable/non-abelian one is
   measured at LLPO.

So the new datum is: **the inverse-limit universal property = the meet's GLB (built), the abelian profinite
group = a built family-Cauchy limit, and the Stone tie calibrates the non-abelian/uncountable boundary at
LLPO.** No re-skin — three ties (universal property, abelian build, calibrated boundary) the neighbors lacked.

## Revelation (collapse + forcing + spine)

**Collapse + forcing + the spine, with the group leg PREDICTION and a built abelian surprise.** A profinite
group is ONE `⟨C | L_lim⟩ ⊕ Residue`: `padic.md`'s resolution `C` (an inverse system of finite count-Lens
readings) read through the meet-of-the-family `L_lim`, leaving the reached-by-none completion residue, on the
`stone_duality.md` calibrated boundary. Four moves at once:

1. **Collapse — the inverse limit IS the meet of the finite-quotient family.** `lim G_i`, the meet
   `iProdLens F`, `padic.md`'s completion, and `CompletionTower`'s tower-of-completions are **one object**:
   the family-reading's limit. `iProdLens_is_greatest_pw` proves the meet has the inverse limit's universal
   property; `tower_is_single_inner` (by `rfl`) proves completion = inverse limit returns home; `GenericFamily`
   proves profinite and archimedean completions are the same mechanism at two `base`-fillings. No new
   primitive — the inverse limit is the resolution-tower meet.

2. **Forcing — the universal property is FORCED as the meet's GLB.** Given the inverse system as a Lens-family,
   "the limit factors through every finite stage" is not an axiom but the greatest-lower-bound property of the
   meet (`iProdLens_refines_each` = the cone, `iProdLens_is_greatest_pw` = terminality). The inverse-limit
   universal property is the meet's GLB, built ∅-axiom.

3. **Residue surfaced — the completed point is the reached-by-none modulus, q=+1 converge.** A profinite
   element (a compatible thread) is reached by no finite quotient, only narrowed to — the `padic`/Iwasawa
   completion residue, tagged `q=+1` (the all-zero profinite zero is the inhabited fixed-point thread;
   `odo_no_fixpoint` the `q=−1` reminder). μ = the finite-stage truncations; the limit never is.

4. **The spine — profinite=Stone puts the limit on the calibrated ultrafilter/LLPO boundary.** The finite
   quotients are the Boolean/`decide` side (∅-axiom, each a finite count); the inverse limit as a compact
   Stone space is the points-from-readings reconstruction at the maximal index = the SAME boundary
   `stone_duality.md`/`nonstandard_analysis.md` calibrated at LLPO. The abelian/countable build dodges it;
   the general profinite group's compactness measures it at BPI/LLPO. **Honest:** the *group law on the
   limit*, the Krull topology as a named object, and the absolute Galois group are PREDICTION/ABSENT — the
   meet (thread space) is built, the group multiplication welded onto it pointwise is not a named object.

## The precise located boundary

Two distinct edges, both honest:
- **The non-abelian/uncountable group structure on the limit (PREDICTION/ABSENT).** `iProdLens` builds the
  thread *space* and its universal property; a `ProfiniteGroup` type bundling the inverse limit with a
  *group law* (multiplication, inverse, the Krull topology making it a topological group) is **absent**
  (grep-confirmed: zero `ProfiniteGroup`/`inverseLimit`/`absoluteGalois`/`Krull` declarations). The abelian
  case is built (ℤ̂, ℤ₂); the non-abelian general group is the open object.
- **The Stone/compactness side (calibrated at LLPO, `stone_duality.md`).** Every profinite group is compact
  (= a Stone space); in full generality this is the BPI/LLPO-strength totalization with no ∅-axiom witness
  (`comparability_imp_llpo`). The finite-quotient Boolean side is PURE; the completed-limit-as-compact-space
  side is the calibrated exterior — the same boundary the ultrafilter/Stone space sits on, measured not
  posited.

## VALIDATE — verdict

**PREDICTION + a genuine BUILT surprise (the abelian inverse limit + the universal property) + a located
boundary at the Stone/group side (calibrated at LLPO). No break, no new axis; model v7.1 holds.** A profinite
group predicts and consolidates: G = lim G_i is `padic.md`'s resolution tower (BUILT, `CompletionTower`), the
inverse-limit universal property is the meet's GLB (BUILT, `iProdLens_is_greatest_pw`), the abelian profinite
group ℤ̂/ℤ₂ is a built family-Cauchy limit (BUILT, `ProfiniteSeq`/`OdometerValue` — the surprise), and the
profinite=Stone tie puts it on the calibrated ultrafilter/LLPO boundary (`stone_duality.md`). The located
boundary is the **non-abelian group law on the limit** (`ProfiniteGroup`/Krull/absolute-Galois ABSENT) and
the **full compactness/Stone side** (LLPO/BPI). No new primitive — `C` is `padic.md`'s resolution iterated
into an inverse system, `L_lim` is the meet of the finite-quotient family, the residue is the completion
modulus on the Stone boundary.

## Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213` this session; purity scanned via `tools/scan_axioms.py` from repo root)

| Leg | Theorem (file:line : name) | Status |
|---|---|---|
| ★★★ **abelian profinite group ℤ̂ = lim ℤ/m BUILT (the surprise) — family-Cauchy + profinite zero** | `Lib/Math/Analysis/Cauchy/ProfiniteSeq.lean:122 factorial_seq_familyCauchy`, `:89 factorial_seq_cauchy`, `:105 factorial_seq_limit_zero`, `:131 factorial_seq_limit_all_zero` (the profinite zero of ℤ̂), `:58 factorial_dvd` | **∅-axiom PURE, scanned 9/0** ✓ |
| ★★★ **inverse-limit OBJECT = the meet of the finite-quotient Lens-family; its universal property = the meet's GLB** | `Lens/Lattice/IndexedJoin.lean:97 iProdLens` (the thread space), `:106 iProdLens_view`, `:149 iProdLens_refines_each` (the projection cone), `:168 iProdLens_is_greatest_pw` (terminal/universal half) | **∅-axiom PURE, scanned 8/0** ✓ |
| ★★ **profinite ↔ archimedean = two Lens-family choices, one limit mechanism** | `Lib/Math/Analysis/Cauchy/GenericFamily.lean:115 profinite_factorial_is_GFCauchy`, `:82 orderCauchy_is_GFCauchy`, `:40 GFCauchy`, `:59 limitAssign_eq_tail`, `:147 projectionLens_view` | **∅-axiom PURE, scanned 10/0** ✓ |
| ★★ **ℤ₂ = lim ℤ/2ᵏ quantitatively — the odometer is the profinite successor `+1 mod 2ᵏ`** | `Theory/Raw/OdometerValue.lean:74 bval_odo` (the profinite successor), `:105 odo_no_fixpoint` (the `+1` fixes no point, q=−1), `:29 bval`, `:40 bval_congr` | **∅-axiom PURE, scanned 16/0** ✓ |
| ★ **the inverse limit as the family-reading's limit (family-Cauchy + limit assignment + agrees with iProdLens)** | `Lens/Instances/Cauchy.lean:105 FamilyCauchy`, `:110 LimitAssignment`, `:115 LimitAssignment.limit`, `:124 pointwise_limit_match`, `:63 eventually_class_unique`, `:88 limitClass_eq_tail` | **∅-axiom PURE, scanned 15/0** ✓ |
| ★★ **completion = inverse limit, returns home with the modulus ascending (Leg 1)** | `Lib/Math/Analysis/CompletionTower.lean:89 tower_is_single_inner` (`rfl`), `:99 tower_stays_in_cut`, `:113 tower_value_stable`, `:57 completion_idempotent` | **∅-axiom PURE, scanned 7/0** ✓ |
| ★ **the level grades ADD up the tower `(ℕ,+)` (Leg 1)** | `Lib/Math/Analysis/ResolutionShift.lean:130 IsResolutionShift_compose`, `:73 IsResolutionShift` | **∅-axiom PURE, scanned 17/0** ✓ |
| ★ **ℤ_p = lim ℤ/pⁿ — the p-adic resolution tower (base=p)** | `Lib/Math/NumberSystems/Padic/Foundation.lean:41 ZpSeq`, `:52 ZpSeq.trunc`, `:65 Zp.diagLimit`, `:75 Zp.diagLimit_trunc_succ` | ∅-axiom (per `padic.md`, Padic INDEX ~484/0) ✓ |
| the absolute-Galois bottom rung (cyclotomic abelian Galois group) | `Lib/Math/Algebra/Icosahedral/CyclotomicFive.lean:66 galois_group_is_C4` (`Gal(ℚ(ζ₅)/ℚ)≅C₄`), `:79 golden_real_subfield` | ∅-axiom (4/0, per `class_field_theory.md`) ✓ |
| ★ **profinite=Stone → the calibrated ultrafilter/LLPO boundary (the spine; the general compactness)** | `Lib/Math/Logic/RealComparabilityLLPO.lean:33 comparability_imp_llpo`; `Lib/Math/Logic/RealDichotomyLLPO.lean:525 llpo_of_realDichotomy` | ∅-axiom PURE (2/0, 31/0; per `stone_duality.md`) ✓ |
| the q=+1 completion residue / q=−1 escape tag | `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag`, `:86 multiplier_unimodular`, `:133 escape_residue_outside`, `:160 converge_residue_fixed`, `:180 golden_is_converge`, `:228 residue_tag_two_poles` | ∅-axiom PURE (55/0) ✓ |
| the reached-by-none residue (what the Stone space reifies) | `Lens/Foundations/FlatOntologyClosure.lean:47 object1_injective`, `:61 object1_not_surjective`, `:69 self_covering_closure` | ∅-axiom PURE (per `stone_duality.md`) ✓ |
| compactness = finiteness collapse (the Stone-space property, finite side) | `Lib/Math/Geometry/Topology/Compactness.lean:42 heineBorel`, `:66 compact_bounded_by_length` | ∅-axiom (per `topology.md`) ✓ |

**Fresh purity scans (this session, `tools/scan_axioms.py` from repo root):**
`E213.Lib.Math.Analysis.Cauchy.ProfiniteSeq` — **9 pure / 0 dirty** (incl. `factorial_seq_familyCauchy`,
`factorial_seq_limit_all_zero`). `E213.Lens.Lattice.IndexedJoin` — **8 pure / 0 dirty** (incl. `iProdLens`,
`iProdLens_is_greatest_pw`). `E213.Lib.Math.Analysis.Cauchy.GenericFamily` — **10 pure / 0 dirty** (incl.
`profinite_factorial_is_GFCauchy`, `orderCauchy_is_GFCauchy`). `E213.Theory.Raw.OdometerValue` —
**16 pure / 0 dirty** (incl. `bval_odo`, `odo_no_fixpoint`). `E213.Lens.Instances.Cauchy` —
**15 pure / 0 dirty** (incl. `FamilyCauchy`, `LimitAssignment`, `pointwise_limit_match`).
`E213.Lib.Math.Analysis.CompletionTower` — **7 pure / 0 dirty**. `E213.Lib.Math.Analysis.ResolutionShift` —
**17 pure / 0 dirty**. `E213.Lib.Math.Foundations.ResidueTag` — **55 pure / 0 dirty**.

## Dropped / flagged citations (honest — NOT grounded in repo Lean)

- **`ProfiniteGroup` / `profinite_group` as a named type with a GROUP law — ABSENT** (grep over all
  `lean/E213`: zero declarations). `ProfiniteSeq`/`GenericFamily`/`OdometerValue` build the *abelian additive*
  inverse limit (ℤ̂, ℤ₂ — `+1 mod 2ᵏ`, `0 mod m`) and `iProdLens` builds the thread *space* with its
  universal property, but a profinite *group* type bundling the inverse limit with multiplication/inverse and
  the Krull topology is not built. The only `profinite` declaration is `profinite_factorial_is_GFCauchy`
  (`GenericFamily.lean:115`); the rest are docstrings (`ProfiniteSeq`, `OdometerValue`). PREDICTION for the
  group leg, BUILT for the abelian inverse limit.
- **`inverseLimit` / `inverse_limit` / `projectiveLimit` / `projective_limit` as named objects — ABSENT**
  (grep-confirmed). The inverse limit IS built, but as the *meet* `iProdLens` / the family-Cauchy limit, not
  under those names. The universal property is `iProdLens_is_greatest_pw`, not a named `inverseLimit.lift`.
- **`absoluteGalois` / `absolute_galois` / `Gal(K̄/K)` as a named object — ABSENT** (grep-confirmed). The
  bottom rung `Gal(ℚ(ζ₅)/ℚ)≅C₄` is built (`galois_group_is_C4`); the infinite profinite Galois tower
  `lim Gal(L/K)` is the open object (the same edge `iwasawa_theory.md` flagged for the ℤ_p-extension).
- **`KrullTopology` / `krull_topology` / `totally_disconnected` / `totallyDisconnected` as named objects —
  ABSENT** (grep-confirmed). The Krull topology is the conceptual reading "open ⟺ finite-index ⟺ a
  finite-stage fibre" (`stone_duality.md`'s clopen↔element); compactness (the Stone-space property) is built
  only on the finite/dyadic side (`heineBorel`), with the full profinite compactness the LLPO/BPI boundary.
- **The general (non-abelian/uncountable) profinite group's compactness as a Stone space — LLPO/BPI
  boundary, no ∅-axiom witness.** `comparability_imp_llpo`→`llpo_of_realDichotomy` calibrate it; not claimed
  as built. The countable abelian case is built; the general case is the calibrated exterior, the same one
  `stone_duality.md` located.

## Verified buildable witness (suggested, NOT built this session)

A **two-quotient inverse-limit thread with its universal property**, instantiating `iProdLens` on the family
`{leavesModNat 2, leavesModNat 3}` (= ℤ/2 × ℤ/3 ≅ ℤ/6 as a finite inverse-limit stage) and exhibiting the
compatible-thread = `iProdLens.view` agreement (`pointwise_limit_match`) with `iProdLens_is_greatest_pw`
as the explicit universal property at index 2 and 3 — the finite-stage warm-up to the ℤ̂ build, making the
"inverse limit = meet, universal property = GLB" identification a worked two-index instance. Optionally tag
the all-zero profinite-zero thread `converge` (`q=+1`) via `ResidueTag` against `odo_no_fixpoint`'s `escape`
(`q=−1`). Flagged as the located target; not built this session.

## Verdict: PREDICTION + built abelian surprise + located boundary at the group/Stone side

A profinite group **predicts and consolidates, with a genuine ∅-axiom surprise** — no break, no new axis.
**Grounded ∅-axiom (the surprises):** the abelian profinite group ℤ̂ = lim ℤ/m as a family-Cauchy limit with
the profinite zero (`ProfiniteSeq.factorial_seq_limit_all_zero`, 9/0); ℤ₂ = lim ℤ/2ᵏ quantitatively, the
odometer the profinite successor `+1 mod 2ᵏ` (`OdometerValue.bval_odo`, 16/0); the inverse-limit OBJECT as the
meet of the finite-quotient Lens-family and its **universal property as the meet's greatest-lower-bound**
(`iProdLens_is_greatest_pw`, 8/0); profinite ↔ archimedean as two Lens-family choices, one limit mechanism
(`GenericFamily`, 10/0); completion = inverse limit returning home with the modulus ascending
(`CompletionTower.tower_is_single_inner`, 7/0) and the level grades adding `(ℕ,+)`
(`IsResolutionShift_compose`, 17/0); ℤ_p = lim ℤ/pⁿ (`padic` ZpSeq); the absolute-Galois bottom rung
(`galois_group_is_C4`, 4/0). **PREDICTION / located boundary:** the non-abelian group law on the limit, the
Krull topology, the absolute Galois tower, and the named `ProfiniteGroup`/`inverseLimit`/`absoluteGalois`
objects (all grep-confirmed absent); the full profinite compactness/Stone-space side (calibrated at LLPO,
`comparability_imp_llpo`→`llpo_of_realDichotomy`, the same boundary `stone_duality.md` located). The thesis
holds and is grounded harder than predicted: **a profinite group = the resolution-tower inverse limit (the
meet of finite groups, `CompletionTower`/`iProdLens`) = the modulus of finite approximations (reached-by-
none, `continued_fractions` doctrine), with the profinite=Stone tie placing it on the calibrated
ultrafilter/LLPO boundary** — NO new primitive; it is the resolution-tower meet, the abelian case built, the
non-abelian/Stone case calibrated. **Profinite groups EXTEND by consolidation (PREDICTION) with a built
abelian inverse-limit surprise; the group law on the limit and the full Stone compactness are the located
boundary.**
