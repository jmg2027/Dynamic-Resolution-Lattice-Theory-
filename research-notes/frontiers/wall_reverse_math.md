# Frontier: the `CompleteMetricModulus` wall — reverse-math / proof-theory pinpoint

Status: OPEN (diagnostic). No Lean edited. The wall is an *interface* defect,
not a hole in the fixed-point mathematics.

## The wall, stated from the actual signatures

`lean/E213/Lib/Math/Analysis/BanachFixedPoint.lean:183-189`:

```
structure CompleteMetricModulus (X : Type) extends MetricModulus X where
  lim : (Nat → X) → X                                  -- TOTAL, no Cauchy hyp
  climconv : ∀ (seq : Nat → X),
    (∀ m, ∃ N, ∀ p q, p ≥ N → q ≥ N → close m (seq p) (seq q)) →
    ∀ m, ∃ N, ∀ p, p ≥ N → close m (seq p) (lim seq)
```

`lim` is a function on **every** bare sequence `Nat → X`; `climconv` then
asserts that for **every** sequence that *happens* to satisfy the Cauchy
predicate, that same `lim` lands on a genuine limit. The Cauchy property is a
*hypothesis discharged later*, not an *input to `lim`*. That ordering is the
whole problem.

`DyadicCompletion.lean` (`lean/E213/Lib/Math/Probability/Limit/DyadicCompletion.lean`)
builds every surrounding piece honestly and ∅-axiom:
- `DyC L` (carrier = regular `dyMet`-Cauchy sequence, line 54-58),
- `metC L` (completion metric, line 90-95),
- `Φhat_contraction` (line 316-322, the convolve-rescale map is a genuine
  `Contraction (metC L)`),
- the *total* stabilizing diagonal `stab`/`limPoint` (line 222-257),
- `orbit_to_center_completion` (line 354-370, the Gaussian center reached as a
  `closeC`-limit of the Picard orbit).

But grep confirms (`completeDy` appears **only** at line 30 as prose) that the
file never assembles `completeDy : CompleteMetricModulus (DyC L)` and never
proves `climconv`. The only inhabited `CompleteMetricModulus` in the repo is the
one-point `trivComplete` on `Unit` (`BanachFixedPoint.lean:290`). The header
*plans* a `climconv` "quarter-triangle / 3ε argument" (lines 27, 215) that is
not carried out. **That gap is the wall.**

## 1. What the bare `lim` + universal `climconv` smuggles

Read the type of `lim` as a uniform operator. `lim : (Nat → X) → X` together
with the *promise* that it converges on every Cauchy sequence is exactly the
statement:

> from the bare existence of a Cauchy sequence (`∀ m, ∃ N, ...`, modulus
> existentially quantified and re-chosen per `m`), extract a single point of the
> completion that the sequence approaches.

The hypothesis `∀ m, ∃ N, ∀ p q ≥ N, close m (seq p) (seq q)` is
**Cauchy-without-a-modulus**: for each precision `m` a cutoff `N` is *asserted to
exist*, but no function `m ↦ N(m)` is given. Turning that `∀m ∃N` into a usable
limit requires selecting, uniformly in `m`, a witness `N(m)` from the
`∃ N` — i.e. a choice function over `Nat`.

Precise principle: **countable choice for the natural numbers, `AC₀,₀` (a.k.a.
`ACω` restricted to `Nat`-indexed `Nat`-valued relations)** — equivalently in the
Bishop/constructive idiom, the assumption that **"every Cauchy sequence has a
modulus of Cauchyness."** In second-order arithmetic terms the bare-`lim`
completion statement (every Cauchy real / Cauchy sequence in a complete space
has a limit, *without* a supplied rate) is the **arithmetical** form whose proof
needs a choice/comprehension step beyond `RCA₀`'s `Δ⁰₁`-comprehension: you must
produce the Skolem function `N(·)` and then the limit. The bare `lim` is a
*Skolemized* `climconv` smuggled in as data — it pretends the choice was already
made for all sequences at once (a uniform `(Nat→X)→X`), which is even stronger
than `AC₀,₀` (it is a *global* choice / selection operator on the function
space, choice-free only when the carrier supplies the witness intrinsically).

Constructively, the separating fact is classical: classical logic + `AC₀,₀`
proves "Cauchy ⟹ Cauchy-with-modulus" trivially (least-`N` search closed under
`∃`), so the bare `lim` is *classically trivial* — which is precisely why it is
constructively (and hence ∅-axiom) **out of reach**: it is provable only with
the very choice/omniscience the discipline forbids.

## 2. The modulated statement needs none of this

Contrast `picard_cauchy` (`BanachFixedPoint.lean:154-174`). Its conclusion is

```
∀ m, ∃ N, ∀ p q, p ≥ N → q ≥ N → M.close m (picard T x0 p) (picard T x0 q)
```

but the proof produces `N := m` explicitly (`refine ⟨m, ?_⟩`, line 159). The
existential is *immediately witnessed by a computed function of `m`* — there is
no `∃` to choose from, the modulus `N(m)=m` is **constructed** from the
contraction's geometric tail (`picard_tail`, `cmono_le`). A contraction
**supplies its own modulus**: each `T`-application advances one dyadic scale
(`picard_step_geometric`, line 45), so the rate is forced data, never a choice.

The same shape is everywhere the repo touches completeness:
- `CauchyCutSeq` (`Analysis/CauchyComplete.lean:38-45`) carries
  `N : Nat → Nat → Nat` **as a structure field**, and `limit` is
  `fun m k => cs (N m k) m k` (line 44-45) — the limit is read off by *evaluating
  the supplied modulus*, with no search and no choice. The header records the
  user insight verbatim: "Since Real213 itself is (sequence + modulus), Cauchy
  completeness is *almost trivial*."
- `DyC L` (`DyadicCompletion.lean:54-58`) bakes the modulus into the *regular*
  convention (Bishop): `closeDy L m (seq p)(seq q)` for all `p,q ≥ m` — the
  identity function `m ↦ m` is the modulus, structurally. No `∃N`.
- `Bridge/CauchyModulus.lean:39-44` (`ProbCauchy`) again carries `N : Nat → Nat`
  as a field.

So every Cauchy object 213 actually manipulates is a **regulated/modulated**
sequence — a `(sequence, modulus)` pair — for which the limit operator is a
total, choice-free *evaluation*, not a selection.

The right Banach fixed-point theorem therefore quantifies over **modulated
sequences** (or, better, over **contractions**, which generate their own
modulus). `banach_fixed_point` (line 202-237) is *already* of this kind on its
own terms — it only invokes `climconv` on `picard T x0`, a sequence whose
modulus `picard_cauchy` hands over explicitly. The fixed point is
`lim (picard T x0)`; the only thing forcing a choice is that `lim` was typed to
accept *bare* sequences. Feed `lim` the *modulus too* and the choice evaporates.

## 3. Proof-theoretic verdict

(a) **Bare `lim` + universal `climconv` is NOT provable ∅-axiom.** It Skolemizes
   "every Cauchy sequence (modulus existentially quantified) converges" into a
   single total operator, which requires `AC₀,₀` / "Cauchy ⟹ has-a-modulus"
   (countable choice over `Nat`), a principle unavailable without
   `Classical.choice`. Hence any honest `completeDy` built to this signature on
   a non-trivial carrier would be axiom-dirty (or impossible quotient-free) —
   exactly why the file stops at the comment and only `Unit` instantiates it.

(b) **The modulated Banach fixed-point theorem IS provable ∅-axiom** and is in
   the repo: `picard_cauchy` (∅-axiom, witness `N(m)=m`) + a *modulated*
   completeness assumption (limit-of-a-sequence-**with-its-modulus**) give the
   located fixed point with no choice. This is the `RCA₀` / `BISH` content:
   contraction-mapping with an explicit Lipschitz/rate constant is a theorem of
   `RCA₀` and of Bishop constructive analysis — no `WKL₀`, no choice. The Lean
   evidence that the witness is *data not search*: `CauchyCutSeq.limit`
   evaluates a stored modulus (`CauchyComplete.lean:44`); `picard_cauchy`
   refines `⟨m, …⟩`.

(c) **The dividing line** is precisely *modulus-as-existential* vs
   *modulus-as-data*. `∀m ∃N. Cauchy_N` (bare) sits above `RCA₀` (needs
   `AC₀,₀`); `∃(N:Nat→Nat). ∀m. Cauchy_{N(m)}` (modulated) is `Δ⁰₁` once `N` is
   in hand and is `RCA₀`-/`BISH`-provable. One-paragraph why the modulated
   version is choice-free: the modulus `N` is a **constructed function** — for a
   contraction it is literally `m ↦ m` (`picard_cauchy`), for a `CauchyCutSeq`
   it is a field of the structure — so the limit is obtained by **applying** `N`
   and then evaluating the sequence at `N(m)` (`limit = cs (N m k) m k`), a
   primitive-recursive read-off. No witness is *chosen*: it is *supplied*. The
   bare version asks logic to manufacture that function from a non-uniform
   family of `∃`-claims, which is the choice step the discipline correctly
   refuses.

## What to state instead (recommendation)

Re-type completeness so the modulus is an input, not a post-hoc hypothesis. Two
equivalent ∅-axiom-friendly shapes:

1. **Modulated `lim`:** `lim : (seq : Nat → X) → (∀ m, ∃ N, …) → X` (limit takes
   the Cauchy proof — which, in 213, is itself a constructed modulus — as an
   argument), or more honestly
   `lim : (seq : Nat → X) → (mod : Nat → Nat) → (regularity-of mod) → X`.
2. **Regulated carrier (already built):** drop `CompleteMetricModulus` for the
   non-trivial case and state the headline directly on `DyC L` /
   `CauchyCutSeq`, where the modulus is structural. `orbit_to_center_completion`
   already *is* the genuine fixed-point content on `DyC L` without ever touching
   the bare `lim`. Promoting that (plus a `Φhat`-fixed-point corollary phrased
   on `metC L`) discharges the Banach headline for convolve-rescale with no
   `CompleteMetricModulus` instance at all.

Either way the theorem the repo *should* state quantifies over
modulated/regulated sequences (or contractions), and is ∅-axiom **precisely
because it never invokes the `AC₀,₀` that the bare `lim` silently demands**.

## Verified citations
- `BanachFixedPoint.lean:183-189` (`CompleteMetricModulus`, bare `lim` + `climconv`)
- `BanachFixedPoint.lean:154-174` (`picard_cauchy`, witness `N(m)=m`)
- `BanachFixedPoint.lean:202-237` (`banach_fixed_point` uses `climconv` only on `picard`)
- `BanachFixedPoint.lean:290-308` (only `trivComplete`/`Unit` instantiates it)
- `DyadicCompletion.lean:30` (`completeDy` is prose only — never defined)
- `DyadicCompletion.lean:54-58, 90-95, 316-322, 222-257, 354-370` (all pieces but no `climconv`)
- `Analysis/CauchyComplete.lean:8-9, 38-45` (modulus as field; "almost trivial")
- `Bridge/CauchyModulus.lean:39-44` (`ProbCauchy`, modulus as field)
