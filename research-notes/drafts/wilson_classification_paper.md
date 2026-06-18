# An elementary, group-theory-free, axiom-free proof of the generalized Wilson theorem

**Draft research note / paper kernel.** Author: Mingu Jeong (theory), with machine
formalization. Target venues: expository (*American Mathematical Monthly*,
*Mathematics Magazine*) for the elementary argument; or a formalization venue
(*ITP*/*CPP*/*JAR*) foregrounding the axiom-free Lean 4 development.

> **Honest novelty statement.** The *theorem* (Gauss's generalization of Wilson's
> theorem) is classical. The claimed contributions are: **(i)** a proof of the
> `+1` case that uses *no group theory and no order/structure facts about the
> square-roots-of-unity group* — in particular it never uses Lagrange's theorem or
> that `|S| = 2^m`; and **(ii)** a complete formalization in Lean 4 that depends on
> **zero axioms** (no `propext`, `Classical.choice`, `Quot.sound`, function
> extensionality, or quotient types — verified by `#print axioms`), which is
> unusual for a result of this depth.
>
> **Literature check (done, 2026-06-18; see `publishability_audit.md`).** The `+1`
> theorem is Miller's 1903 result (*Ann. Math.* 4(4):188–190): the product of all
> elements of a finite abelian group is the unique involution if one exists, else the
> identity. The `P ≡ t^{|S|/2}` pairing move is *that result de-grouped* — known
> folklore (the standard fixed-point-free-involution device), not a new idea; the
> mainstream expositions (Sury, walker) deliberately keep the group language because
> it is cleaner. So contribution (i) is **expository at best** (a *Monthly/Math-Mag*
> note), and referees will cite Miller 1903. The only durable artifact is **(ii)**, the
> ∅-axiom / Mathlib-free / `Classical`-free formalization — and that too is a
> *formalization*-paper contribution (ITP/CPP/JAR), not new mathematics.

## 1. Statement

For `n ≥ 1` let `U(n) = {1 ≤ a ≤ n : gcd(a,n) = 1}` be the units mod `n`, and
`W(n) = ∏_{a ∈ U(n)} a (mod n)`. Gauss:

> **Theorem (generalized Wilson).** `W(n) ≡ −1 (mod n)` iff `n ∈ {1, 2, 4, pᵏ, 2pᵏ}`
> for an odd prime `p`; otherwise `W(n) ≡ +1 (mod n)`.

The case `n = p` prime is Wilson's `(p−1)! ≡ −1 (mod p)`.

## 2. The reduction to square roots of unity

Let `S(n) = {x ∈ U(n) : x² ≡ 1 (mod n)}`, the **square roots of unity**. Each
`x ∈ S(n)` is its own inverse, so in the product `W(n)` every non-self-inverse unit
cancels against its (distinct) inverse. Hence

> **Lemma 1.** `W(n) ≡ ∏_{x ∈ S(n)} x (mod n)`.

(Formalized: `WilsonGeneralization.units_prod_eq_selfinv_prod`, via an explicit
inverse-pairing involution on the residues — no quotient ring `ℤ/n`.)

So `W(n) ≡ P(n) := ∏_{x ∈ S(n)} x`, and everything reduces to the value of `P(n)`.

## 3. The value of `P(n)` — the group-theory-free argument

Note `S(n)` is closed under multiplication mod `n` and every element is an
involution. Classically `S(n) ≅ (ℤ/2)^m` and one computes `P(n)` from the *rank*
`m`. We avoid this entirely.

> **Lemma 2 (pairing-accumulation).** For any **nontrivial** `t ∈ S(n)` (`t ≠ 1`),
> `P(n) ≡ t^{|S(n)|/2} (mod n)`.

*Proof.* The map `σ_t : s ↦ st mod n` is an involution on `S(n)` (`σ_t² = id` as
`t² ≡ 1`) and is **fixed-point-free**: `s ≡ st` would give `t ≡ 1` (cancel the unit
`s`), false. So `σ_t` partitions `S(n)` into 2-element orbits `{s, st}`, of which
there are `|S(n)|/2`. Each orbit contributes `s·(st) = s²t ≡ t`. Multiplying,
`P(n) ≡ t^{|S(n)|/2}`. ∎

(Formalized: `WilsonPlusOne.prodMod_pair_accum`, a fuel recursion that peels orbits
and accumulates one factor `t` each.)

> **Proposition 3.** If `S(n)` has a square root of unity other than `±1` (i.e.
> `|S(n)| ≥ 4`), then `P(n) ≡ +1`. If `S(n) = {1, n−1}`, then `P(n) ≡ −1`.

*Proof.* Write `k = |S(n)|/2`. Since every `t ∈ S(n)` satisfies `t² ≡ 1`,
`t^k ≡ 1` if `k` is even and `t^k ≡ t` if `k` is odd.

- `S(n) = {1, n−1}`: then `P(n) = 1·(n−1) ≡ −1`.
- `|S(n)| ≥ 4`: there are two *distinct* nontrivial elements `t₁ ≠ t₂`. Lemma 2
  gives `P(n) ≡ t₁^k` and `P(n) ≡ t₂^k`. **If `k` were odd**, then `t₁ ≡ P(n) ≡ t₂`,
  contradicting `t₁ ≠ t₂`. So `k` is **even**, whence `P(n) ≡ t₁^k = (t₁²)^{k/2} ≡ 1`. ∎

The crux is the last paragraph: *the mere existence of two distinct nontrivial
square roots forces `|S(n)|/2` even*, and that — not any count of the group order —
delivers `+1`. No Lagrange, no `|S(n)| = 2^m`.

(Formalized: `WilsonValue.wilson_neg_one_of_sqrt_trivial` and
`WilsonPlusOne.wilson_plus_one_of_nontrivial_sqrt`.)

## 4. Which `n` have only `±1` as square roots of unity

> **Lemma 4.** `S(n) = {1, n−1}` (for `n > 2`) iff `n ∈ {4, pᵏ, 2pᵏ}` (odd `p`).

*`⇐`* (only `±1`):
- `n = pᵏ` (odd `p`): `x² ≡ 1` gives `pᵏ ∣ (x−1)(x+1)`. As `gcd(x−1,x+1) ∣ 2` and
  `p` is odd, the full `pᵏ` divides one factor, so `x ≡ ±1` (`SqrtOnePrimePower`,
  via the `p`-adic valuation `v_p((x−1)(x+1)) ≥ k` with one term unramified).
- `n = 2pᵏ`: `x² ≡ 1 (mod 2pᵏ)` gives `x ≡ ±1 (mod pᵏ)` (above) and `x` is odd;
  the parity selects the unique odd lift mod `2pᵏ`, again `±1` (`SqrtOneTwoPrimePower`).
- `n = 4`: direct.

*`⇒`* (a nontrivial root exists otherwise): if `n ∉ {1,2,4,pᵏ,2pᵏ}` then either
`n = 2^a` with `a ≥ 3`, where `2^{a−1}−1 ∈ S(n) ∖ {±1}`; or `n` admits a coprime
factorization `n = ab` with `a, b > 2`, where the CRT solution of `x ≡ 1 (mod a)`,
`x ≡ −1 (mod b)` lies in `S(n) ∖ {±1}` (`WilsonExistence`, via the explicit
reconstruction `crtSolve`). The case split uses one **uniform** coprime split
`(p^{v_p(n)}, n/p^{v_p(n)})` for `p = minFac(oddpart n)`; the complement is `≤ 2`
only when `n = pᵏ` or `2pᵏ`, both excluded (`WilsonClassification`).

Combining Lemma 4 with Proposition 3 gives the Theorem. ∎

## 5. The formalization (the second contribution)

The entire development is a self-contained Lean 4 arc of 7 modules under
`E213/Lib/Math/NumberTheory/` (`WilsonGeneralization`, `WilsonValue`, `WilsonPlusOne`,
`SqrtOnePrimePower`, `SqrtOneTwoPrimePower`, `WilsonExistence`, `WilsonClassification`),
totaling ~110 lemmas. Every declaration satisfies
`#print axioms <name> → "does not depend on any axioms"` — no `propext`,
`Classical.choice`, `Quot.sound`, `funext`, `native_decide`, `sorry`, and no Mathlib.

Two points of formalization interest:
1. **No quotient ring.** `ℤ/n` is never constructed; all of §2–§4 is residue
   arithmetic on `Nat` with `% n`. The "units group" is the concrete coprime-residue
   list; the inverse-pairing and `σ_t`-pairing are list recursions (Lemma 1, 2).
2. **No decision on an undecidable predicate.** The final `iff`
   (`prod_units_neg_one_iff`) would naively `by_cases` on `PrimitiveRootModulus n`,
   which is not decidable as stated and would import `Classical.choice`. Instead a
   *constructive dichotomy* `classify n : PrimitiveRootModulus n ∨ W(n) ≡ +1` is
   proved by exhibiting, for every `n`, either a primitivity witness or a nontrivial
   square root — keeping the whole theorem axiom-free.

## 6. Why this fits the broader program

This sits inside a larger axiom-free corpus (DRLT/213, ~2000 Lean modules) governed
by a *forcing-vs-bookkeeping* discipline: a classical theorem's ∅-axiom re-derivation
is *evidential* only when the constraint forces a structurally different, more
explicit proof. Generalized Wilson is a clean instance — the `+1` case's standard
proof leans on group structure (`|S| = 2^m`), and removing all axioms (in particular,
having no abstract finite-group library to lean on) forced the elementary
`P ≡ t^{|S|/2}` route, which is arguably the more transparent argument and is the
paper's mathematical kernel.

## Status / next steps
- [x] Literature check on the `P = t^{|S|/2}` / "no Lagrange" Wilson `+1` argument —
      **done** (`publishability_audit.md`). Verdict: Miller 1903; folklore device; the
      math is not new. Only the formalization angle survives.
- [ ] Tighten §4's `⇒` exposition (the uniform `minFac(oddpart n)` split).
- [ ] Framing decision (informed by the audit): fold this into the *single* viable
      paper — the repo-wide **∅-axiom Lean-4-without-Mathlib formalization** paper
      (ITP/CPP/JAR), where group-free Wilson is one worked example of "forcing"
      (no abstract finite-group library → the elementary route is forced). A standalone
      *Monthly* note is possible but low-odds (referees → Miller 1903).
