# Order-invariance for the asynchronous distinction system (Q1)

**Status**: deliverable for SPEC Q1 (task M1), object-primary track (F-obj).
**Inputs**: `rederive/SPEC.md`, `seed/ORIGIN_RAW.md` (§5–§8),
`seed/ORIGIN.md`, the program memo, and the F-obj carrier facts proved in
`rederive/lean/Rederive/Tree.lean`.  Nothing else from the repository.
Classical mathematics is used freely; every classical concept relied on is
recorded in §10 for the bilingual ledger.

**Result in one sentence.**  The asynchronous system of SPEC §2 is
deterministic up to order: the state reached by a finite run depends only on
the *set* of executed events; the executed sets are exactly the finite
downsets of an explicitly presented causal partial order **D**; runs are
exactly the linear extensions of **D** (finite downsets in the finite case,
order-type-ω enumerations in the maximal case); and every maximal (weakly
fair) run executes every event and converges to the same limit
`T∞ = Tree`, `U∞ = ∅`.  This is the precise form of ORIGIN_RAW §6's
rejection of the lockstep foliation: staging is a choice of linear
extension; only **D** is invariant.

---

## 1. Definitions

### 1.1 The carrier and the facts used about it

`Tree` is the F-obj carrier of SPEC §1: the smallest family containing two
atoms `a`, `b` and closed under an unordered pairing `pair{x,y}` of two
*distinct* members.  We use exactly four facts about it.

- **T1 (injectivity on unordered pairs).**  For distinct `x ≠ y` and
  `u ≠ v`: `pair{x,y} = pair{u,v}` implies `{x,y} = {u,v}` (as unordered
  pairs).  Equivalently, the two children are recoverable from a composite.
  *Proved axiom-free as `Tree.pairing_inj` / `Tree.children_pairing` in
  `rederive/lean/Rederive/Tree.lean`.*
- **T2 (composites are not atoms).**  `pair{x,y} ∉ {a, b}` for `x ≠ y`.
  *Proved as `Tree.pairing_ne_a`, `Tree.pairing_ne_b` (same file); also
  `a ≠ b` (`Tree.a_ne_b`, SPEC choice C2).*
- **T3 (size).**  There is a function `|·| : Tree → ℕ` with `|a| = |b| = 1`
  and `|pair{x,y}| = |x| + |y| + 1`.  *Structural recursion on the canonical
  term; the defining equation is symmetric in `x, y`, so unorderedness is
  no obstacle.  Consequences: `|t| ≥ 1`; a composite is strictly larger
  than either child; each tree has finitely many subtrees.*
- **T4 (countability).**  `Tree` is countably infinite.  *Injection into
  finite words over a 4-letter alphabet (print the canonical term);
  infinitude from the strictly-size-increasing chain `a, pair{a,b},
  pair{a, pair{a,b}}, …`.*

Write `P₂(X)` for the set of 2-element subsets of `X`, and `P₂ :=
P₂(Tree)`.  For `p = {x, y} ∈ P₂` write `pair p := pair{x,y}` (well-defined
by unorderedness) and `|p| := |x| + |y|`.

### 1.2 States

A **state** is a pair `s = (T, U)` with `T ⊆ Tree` and `U ⊆ P₂(T)`.
The **initial state** is `s₀ = (T₀, U₀) = ({a, b}, ∅)` (SPEC pin; the
variant `U₀ = {{a,b}}` is treated in §8.1).

### 1.3 Events, enabledness, effect

The **event alphabet** is

    E_all := { link p : p ∈ P₂ } ∪ { resolve p : p ∈ P₂ },

a countably infinite set (T4).  Two events are equal iff they have the same
kind and the same pair.  Note the alphabet is a fixed global set: an event
is a *name*, whether or not it is currently executable.  (SPEC choice C4 is
built into the alphabet: there is no event on a self-pair.  C3 —
enabledness is stateless in history — is built into the next definition,
which reads only the current state.)

**Enabledness** in `s = (T, U)`:

- `link {x,y}` is enabled iff `x, y ∈ T`, `x ≠ y`, `{x,y} ∉ U`, and
  `pair{x,y} ∉ T`.  (The last conjunct is SPEC choice **C1**.)
- `resolve {x,y}` is enabled iff `{x,y} ∈ U`.

**Effect** (a total function on states, defined for every event whether or
not enabled; it is applied only to states where the event is enabled):

    upd_{link p}(T, U)    := (T, U ∪ {p})
    upd_{resolve p}(T, U) := (T ∪ {pair p}, U \ {p})

The effect of an event is a state-update determined by the event's name
alone; it does not read the state beyond its argument.  This makes half of
the Persistence Lemma trivial by construction (§3.2) — the substantive
content is in enabledness-preservation and commutation.

### 1.4 Runs, maximality, weak fairness

A **run** (from `s₀`) of length `L ∈ ℕ ∪ {ω}` is a sequence of events
`ρ = (e_k)_{1 ≤ k < 1+L}` together with the induced states `s_0 := s₀`,
`s_k := upd_{e_k}(s_{k-1})`, such that each `e_k` is enabled in `s_{k-1}`.
Write `E_ρ := {e_k}` for the set of executed events and, when the `e_k`
are pairwise distinct (Corollary 5.2 shows they always are), `pos_ρ(e)` for
the position of `e`, and

    e <_ρ f  :⟺  e, f ∈ E_ρ and pos_ρ(e) < pos_ρ(f)

for the **temporal order** of `ρ`.

An infinite run is **weakly fair** iff there is no event `e` and index `n`
such that `e` is enabled in `s_m` for every `m ≥ n` but `e_m ≠ e` for every
`m > n`.  ("No enabled event is forever neglected", SPEC §2.)

A run is **maximal** iff it is finite and no event is enabled in its final
state, or it is infinite and weakly fair.  (Lemma 6.1 shows the first
disjunct is vacuous: there are no finite maximal runs.)

---

## 2. Basic invariants

Throughout, `s = (T, U)` is a state and `s' = upd_e(s) = (T', U')` for an
event `e` enabled in `s`.

**Lemma 2.1 (well-formedness preserved).**  If `U ⊆ P₂(T)` then
`U' ⊆ P₂(T')`.
*Proof.*  `link {x,y}` adds `{x,y}` with `x, y ∈ T = T'` by its guard;
`resolve` removes an element of `U` and enlarges `T`.  ∎

**Lemma 2.2 (T is monotone; atoms persist).**  `T ⊆ T'`; nothing is ever
removed from `T`; hence along any run `T₀ = {a,b} ⊆ T_k ⊆ T_{k+1}`.
*Proof.*  By inspection of the two effects.  ∎

**Lemma 2.3 (U-dynamics are private to the pair).**  For each `p ∈ P₂`:
the only event that inserts `p` into `U` is `link p`; the only event that
removes `p` from `U` is `resolve p`; the only event that inserts `pair p`
into `T` is `resolve p` (uniqueness of `p` here is T1), and `pair p ∉ T₀`
(T2).
*Proof.*  `link q` inserts exactly `q`; `resolve q` removes exactly `q` and
inserts exactly `pair q`; if `pair q = pair p` then `q = p` by T1; `T₀`
consists of atoms, and `pair p` is not an atom by T2.  ∎

**Lemma 2.4 (guard exclusivity).**  For no state and no `p ∈ P₂` are
`link p` and `resolve p` both enabled.
*Proof.*  `link p` requires `p ∉ U`; `resolve p` requires `p ∈ U`.  ∎

**Lemma 2.5 (post-link invariant).**  Along any run, once `link p` has been
executed, every later state satisfies `p ∈ U ∨ pair p ∈ T`.
*Proof.*  Immediately after `link p`, `p ∈ U`.  Preservation: the only
event removing `p` from `U` is `resolve p` (Lemma 2.3), and its effect
simultaneously inserts `pair p` into `T`; membership of `pair p` in `T` is
permanent (Lemma 2.2).  ∎

---

## 3. Persistence

**Lemma 3.1 (Persistence).**  Let `e ≠ f` be two events, both enabled in a
state `s` with `U ⊆ P₂(T)`.  Then `e` is enabled in `upd_f(s)`.

*Proof.*  Write `s = (T, U)`.  First note that if `e` and `f` carry the
same pair `p`, they have different kinds, and Lemma 2.4 forbids
co-enabledness; so the pairs differ.  Four cases.

1. `e = link {x,y}`, `f = link {u,v}`, `{x,y} ≠ {u,v}`.
   After `f`: `T` unchanged, `U' = U ∪ {{u,v}}`.  Guards of `e`:
   `x, y ∈ T` ✓; `{x,y} ∉ U'` since `{x,y} ∉ U` and `{x,y} ≠ {u,v}` ✓;
   `pair{x,y} ∉ T` unchanged ✓.

2. `e = link {x,y}`, `f = resolve {u,v}`, `{x,y} ≠ {u,v}`.
   After `f`: `T' = T ∪ {pair{u,v}}`, `U' = U \ {{u,v}}`.  Guards of `e`:
   `x, y ∈ T ⊆ T'` ✓; `{x,y} ∉ U ⊇ U'` ✓; for the **C1 guard**
   `pair{x,y} ∉ T'` we need `pair{x,y} ∉ T` (given) **and**
   `pair{x,y} ≠ pair{u,v}`, which holds by **T1 (injectivity)** since
   `{x,y} ≠ {u,v}`.

3. `e = resolve {x,y}`, `f = link {u,v}`.
   After `f`: `U' = U ∪ {{u,v}} ⊇ U ∋ {x,y}` ✓.

4. `e = resolve {x,y}`, `f = resolve {u,v}`, `{x,y} ≠ {u,v}`.
   After `f`: `U' = U \ {{u,v}}`; `{x,y} ∈ U` and `{x,y} ≠ {u,v}` give
   `{x,y} ∈ U'` ✓.  ∎

**Remark 3.2 (in what sense the "effect" is unchanged).**  In this
formulation the effect of an event is by definition (§1.3) a state-update
function `upd_e` depending only on the event's name — `link p` always adds
`p` to `U`; `resolve p` always adds `pair p` to `T` and removes `p` from
`U`.  So "the effect of `e` is unchanged by executing `f`" is *true by
construction* and carries no content beyond the definition.  The
substantive half of the informal statement "remains enabled with unchanged
effect" is (i) enabledness-preservation — Lemma 3.1 — and (ii) that the
*results* agree in either order — Lemma 4.1.  We flag this honestly rather
than dress the definitional half as a theorem.

**Where choice C1 is used.**  Exactly once in the proof of Lemma 3.1: the
C1 guard `pair{x,y} ∉ T` is the **only** enabledness conjunct that another
event's execution can threaten (case 2, where `resolve {u,v}` enlarges
`T`), and its preservation is exactly what requires the carrier fact T1
(child recoverability).  All other conjuncts are preserved for trivial
monotonicity/disjointness reasons.  Note carefully: Persistence itself
would *also* hold under the C1-alternative (drop the `pair{x,y} ∉ T`
conjunct) — case 2 then loses its only nontrivial obligation.  C1 becomes
load-bearing later: it is *necessary* for the once-only property and for
set-determinacy (Theorem 5.3 and §5.5).

**Corollary 3.3 (stability).**  Along any run, if `e` is enabled in `s_k`
then `e` is enabled in every later state until (exclusively) the position
at which `e` itself is executed; if `e` is never executed, it remains
enabled forever.
*Proof.*  Induction along the run using Lemma 3.1 at each step where the
executed event differs from `e`.  ∎

Stability is what makes *weak* fairness the right hypothesis in §6:
enabledness, once acquired, is never toggled off by the environment, so
"enabled continuously from some point on" and "enabled at some point and
never executed" coincide (Remark 6.8).

---

## 4. Commutation (diamond)

**Lemma 4.1 (Diamond).**  Let `e ≠ f` both be enabled in `s`
(`U ⊆ P₂(T)`).  Then `f` is enabled in `upd_e(s)`, `e` is enabled in
`upd_f(s)` (Lemma 3.1 twice), and

    upd_f(upd_e(s)) = upd_e(upd_f(s)).

*Proof.*  As in Lemma 3.1 the pairs differ; write `p ≠ q` for the pairs of
`e, f`.  Three shapes.

1. `e = link p`, `f = link q`:  both orders yield
   `(T, U ∪ {p} ∪ {q})`.  ✓
2. `e = link p`, `f = resolve q` (or symmetrically):  both orders yield
   `(T ∪ {pair q}, (U ∪ {p}) \ {q})`, and since `p ≠ q`,
   `(U ∪ {p}) \ {q} = (U \ {q}) ∪ {p}`.  ✓
3. `e = resolve p`, `f = resolve q`:  both orders yield
   `(T ∪ {pair p, pair q}, U \ {p, q})`.  ✓  ∎

Note the diamond holds for **every** pair of distinct co-enabled events —
there is no conflict anywhere in the system.  Dependence between events
will manifest (§5) purely as *never being co-enabled in the required
order*, not as failure of commutation.  This observation matters for the
Mazurkiewicz assessment in §9.3.

---

## 5. Finite runs: set-determinacy and the causal order D

### 5.1 The state formula

For a finite `E ⊆ E_all` define

    T(E) := {a, b} ∪ { pair p : resolve p ∈ E }
    U(E) := { p : link p ∈ E and resolve p ∉ E }.

**Lemma 5.1 (state formula; no repetition).**  Let `ρ = (e_1, …, e_n)` be a
finite run.  Then the `e_k` are pairwise distinct, and the final state is
`(T(E_ρ), U(E_ρ))`.

*Proof.*  Induction on `n`.  Base: `E = ∅`, `(T(∅), U(∅)) = ({a,b}, ∅) =
s₀`.  ✓  Step: let the claim hold for the prefix with executed set `E`, and
let `e` be enabled in `(T(E), U(E))`.

*Case `e = link p`.*  The guards give `p ∉ U(E)` and `pair p ∉ T(E)`.
From `pair p ∉ T(E)`: `resolve p ∉ E` (contrapositive of the definition of
`T(E)`; no injectivity needed in this direction).  Then `p ∉ U(E)` forces
`link p ∉ E`.  So `e ∉ E` (distinctness extends).  New state:
`(T(E), U(E) ∪ {p})`; and indeed `T(E ∪ {link p}) = T(E)` and
`U(E ∪ {link p}) = U(E) ∪ {p}` because `resolve p ∉ E`.  ✓

*Case `e = resolve p`.*  The guard gives `p ∈ U(E)`, i.e. `link p ∈ E` and
`resolve p ∉ E`; so `e ∉ E`.  New state: `(T(E) ∪ {pair p}, U(E) \ {p})`;
and `T(E ∪ {resolve p}) = T(E) ∪ {pair p}`,
`U(E ∪ {resolve p}) = U(E) \ {p}`.  ✓  ∎

**Corollary 5.2 (once-only; no re-enabling).**  In any run (finite or
infinite) each event is executed at most once; moreover after an event has
been executed it is never again enabled.
*Proof.*  At most once: every finite prefix has pairwise distinct events
(Lemma 5.1).  Never re-enabled: after `link p` executes, every later state
has `p ∈ U ∨ pair p ∈ T` (Lemma 2.5), refuting `link p`'s guard — this is
**C1 at work**: the conjunct `pair p ∉ T` is exactly what keeps the guard
refuted after `p` leaves `U` by resolution.  After `resolve p` executes,
`pair p ∈ T` permanently (Lemmas 2.2, 2.3); re-enabling `resolve p` would
need `p ∈ U` again, i.e. a later `link p` (Lemma 2.3), which is never
enabled again by the previous sentence.  ∎

**Theorem 5.3 (order-invariance, finite case).**  The state reached by a
finite run depends only on the **set** of executed events:  if finite runs
`ρ`, `ρ'` satisfy `E_ρ = E_{ρ'}`, they reach the same state, namely
`(T(E_ρ), U(E_ρ))`.
*Proof.*  Immediate from Lemma 5.1.  ∎

(The theorem can also be derived abstractly from Lemmas 3.1 + 4.1 +
Corollary 5.2 by the standard permutation argument — any two enumerations
of the same finite set of pairwise-commuting, at-most-once events are
connected by adjacent transpositions.  We prefer the explicit formula: it
is stronger — it *names* the state — and it is the shape a proof assistant
wants.)

### 5.2 The causal order D

**Definition 5.4.**  On `E_all`, let `≺` be generated by the two rules

- **(g1)** `link p ≺ resolve p` for every `p ∈ P₂`;
- **(g2)** `resolve q ≺ link p` whenever `pair q ∈ p` (i.e. the tree
  created by `resolve q` is one of the two endpoints of the pair `p`).

Let `≤_D` be the reflexive–transitive closure of `≺`, and
`D := (E_all, ≤_D)`.

**Proposition 5.5 (D is a partial order with finite principal downsets).**
`≤_D` is a partial order; every event has ≤ 2 immediate `≺`-predecessors;
every principal downset `↓e := {f : f ≤_D e}` is finite.  Moreover `D` has
a two-element forced bottom: `link{a,b} <_D resolve{a,b} <_D e` for every
other event `e`.

*Proof.*  Define a rank `φ : E_all → ℕ` by `φ(link p) := 2|p|`,
`φ(resolve p) := 2|p| + 1` (with `|p|` from §1.1/T3).  Each generator
strictly increases `φ`: (g1) adds 1; for (g2) with `pair q ∈ p`, say
`p = {pair q, y}`,

    φ(link p) = 2(|pair q| + |y|) = 2(|q| + 1 + |y|) ≥ 2|q| + 4
              > 2|q| + 1 = φ(resolve q).

Hence `≺` has no cycles, so the reflexive–transitive closure is
antisymmetric (a nontrivial cycle would give a `φ`-increasing loop);
reflexivity and transitivity hold by construction.  Immediate
predecessors: `resolve p` has exactly one (`link p`, by (g1); (g2) never
targets a resolve); `link p` has one for each composite endpoint of `p` —
at most 2 — and the producing pair `q` with `pair q = x` is *unique* for
each composite endpoint `x` by **T1**.  Finiteness of `↓e`: strong
induction on `φ(e)`; `↓e = {e} ∪ ⋃ {↓f : f ≺ e}`, a finite union of sets
finite by induction hypothesis (each `f ≺ e` has `φ(f) < φ(e)`); the
identification of `↓e` uses that any `g <_D e` factors through some
immediate predecessor.  Forced bottom: any event other than the two events
on `{a,b}` involves a composite tree somewhere in its pair; every composite
tree contains `pair{a,b}` as a subtree (a size-minimal composite subtree
has two atom children, which must be `a` and `b` since children are
distinct and there are only two atoms), and chasing (g2)/(g1) down the
subtree structure reaches `resolve{a,b}`, whence `link{a,b}` by (g1).  ∎

**Remark 5.6 (forced opening).**  Correspondingly, at the dynamic level:
in `s₀` the only enabled event is `link{a,b}` (the only 2-subset of `T₀`),
and after it the only enabled event is `resolve{a,b}`.  Every run begins
with these two, and the first genuine choice (`link{a, pair{a,b}}` vs
`link{b, pair{a,b}}`) occurs at step 3.  The system's opening is fully
deterministic — order-freedom is *generated*, not primitive.

### 5.3 Executed sets = finite downsets

Recall a **downset** (order ideal) of `D` is `F ⊆ E_all` with
`f ≤_D e ∈ F ⟹ f ∈ F`.

**Theorem 5.7.**
(i) For every finite run `ρ`, `E_ρ` is a finite downset of `D`, and the
temporal order `<_ρ` extends `<_D` restricted to `E_ρ`
(`e <_D f`, both executed `⟹ e <_ρ f`).
(ii) Conversely, for every finite downset `F` and every linear extension
`ℓ = (e_1, …, e_n)` of `(F, ≤_D)`, the sequence `ℓ` is a run.
Hence: **finite runs = linear extensions of finite downsets of D**, and by
Theorem 5.3 the reached state depends only on the downset.

*Proof.*
(i)  It suffices to show each prefix set `E` stays a downset when an
enabled `e` is added; closure under `≤_D` then follows by induction along
generator chains.  Check the immediate predecessors of `e` lie in `E`
(state formula, Lemma 5.1):

- `e = link {x,y}`: enabled gives `x, y ∈ T(E)`; each composite endpoint
  `x = pair q` thus has `resolve q ∈ E` (definition of `T(E)` + T1);
  atoms need no predecessor.  These are exactly `e`'s (g2)-predecessors.
- `e = resolve p`: enabled gives `p ∈ U(E)`, so `link p ∈ E` — the sole
  (g1)-predecessor.

For the temporal statement: if `e <_D f` and both are executed, every
prefix ending just after `f`'s position is a downset containing `f`, hence
contains `e`; since events occur once (Corollary 5.2), `e`'s position is
earlier.

(ii)  Induction along `ℓ`.  Let `E := {e_1, …, e_k}` (a downset of `F`,
hence of `D`, because `ℓ` is a linear extension) with current state
`(T(E), U(E))` (Lemma 5.1 applied to the run built so far), and consider
`e := e_{k+1} ∉ E` with all `≤_D`-predecessors in `E`.

- `e = link {x,y}`:  every composite endpoint `x = pair q` has
  `resolve q ≺ e`, so `resolve q ∈ E`, so `x ∈ T(E)`; atoms are in `T(E)`
  always.  Guard `{x,y} ∉ U(E)`: membership would need
  `link{x,y} ∈ E`, but `e ∉ E`.  Guard `pair{x,y} ∉ T(E)` (**C1**):
  membership would need `resolve{x,y} ∈ E`; but
  `e = link{x,y} <_D resolve{x,y}` by (g1), and `E ∌ e` is a downset —
  contradiction.
- `e = resolve p`:  `link p ≺ e` gives `link p ∈ E`, and `resolve p = e ∉
  E`; hence `p ∈ U(E)`.  ∎

**Corollary 5.8 (reachable states = finite downsets; a distributive
lattice).**  The map `F ↦ (T(F), U(F))` is a bijection from finite downsets
of `D` onto reachable states.  Consequently the reachable states, ordered
by reachability, form a distributive lattice (meet/join = intersection/
union of downsets), with the run-confluence reading: any two finite runs
can be extended to a common state (execute the union downset).
*Proof.*  Surjectivity is Theorem 5.7 + Lemma 5.1.  Injectivity: from
`(T, U) = (T(F), U(F))` one recovers `F`:
`resolve p ∈ F ⟺ pair p ∈ T` (T1, T2 make `p ↦ pair p` injective with
atom-free image), and `link p ∈ F ⟺ p ∈ U ∨ resolve p ∈ F` (downset
property + formula).  Downsets of a poset are closed under `∪, ∩` and form
a distributive lattice (Birkhoff); reachability order matches inclusion of
downsets by Theorem 5.7(ii) (extend an enumeration of `F` by one of
`F' \ F` when `F ⊆ F'`).  ∎

### 5.4 What the causal order is *of* (events vs occurrences)

Because of Corollary 5.2, an event name occurs at most once in any run, so
"event" and "event occurrence" coincide and `D` is a genuine partial order
on the alphabet itself.  This is a consequence of **C1**, not a triviality
— see §5.5.

### 5.5 C1 is necessary for set-determinacy

Under the C1-alternative (drop the conjunct `pair{x,y} ∉ T` from the link
guard; SPEC §2 table, row C1), Theorem 5.3 is **false**.  Counterexample:
with `p = {a, b}`,

    ρ  = (link p, resolve p)             E_ρ  = {link p, resolve p}
    ρ' = (link p, resolve p, link p)     E_ρ' = {link p, resolve p}

(the third step is enabled in the alternative system since `a, b ∈ T` and
`p ∉ U` there).  Same executed *set*, different final states (`p ∈ U`
after `ρ'`, not after `ρ`).  Order-invariance for the alternative system
can only be stated over *multisets* / occurrence sequences, i.e. one is
forced from the alphabet-poset picture into a genuine occurrence-net
picture.  This quantifies the refutation-track question "what survives
under the C1-alternative": Persistence (Lemma 3.1) and the Diamond (Lemma
4.1) survive verbatim (their proofs never used the C1 conjunct except to
preserve it); once-only (Corollary 5.2), the state formula as a function of
sets (Lemma 5.1), set-determinacy (Theorem 5.3), and the downset bijection
(Corollary 5.8) all fail as stated.

---

## 6. Infinite runs, fairness, and the limit

### 6.1 There are no finite maximal runs

**Lemma 6.1.**  Every reachable state has an enabled event; hence every
maximal run is infinite (of length ω).
*Proof.*  Let `(T, U)` be reachable; `T` is finite (Lemma 5.1) and contains
`a ≠ b`.  If `U ≠ ∅`, any `p ∈ U` gives enabled `resolve p`.  If `U = ∅`,
pick `t ∈ T` of maximal size and any other `u ∈ T` (exists, `|T| ≥ 2`);
then `pair{t,u}` has size `|t| + |u| + 1 > |t|` (T3), so `pair{t,u} ∉ T`,
and `{t,u} ∉ U = ∅`; so `link{t,u}` is enabled.  ∎

### 6.2 Enumeration lemmas (classical order theory, proved for
self-containment)

**Lemma 6.2 (finite topological sort).**  Every finite poset has a linear
extension.
*Proof.*  Induction on size: a finite nonempty poset has a minimal element
(iterate strict descent; finiteness + antisymmetry force termination);
output it, recurse.  ∎

**Lemma 6.3 (ω-extension / natural labeling).**  Let `P` be a countably
infinite poset in which every principal downset is finite (e.g. `D`, or
any infinite downset of `D`).  Then `P` has a linear extension of order
type ω: a bijective enumeration `x_1, x_2, …` of `P` with
`x_i <_P x_j ⟹ i < j`.
*Proof.*  Fix a surjection `ν : ℕ → P` (countability).  Maintain a finite
output list, initially empty, whose set is always a downset and whose
order is always compatible with `<_P`.  At stage `k`, append the elements
of `↓ν(k) ∖ (already output)` in some linear extension of their induced
order (finite, Lemma 6.2).  Compatibility: when an element `x` is
appended, every `y <_P x` lies in `↓ν(k)` (transitivity), hence is already
output or scheduled earlier within the stage (linear-extension order).
Every prefix is a downset for the same reason.  Bijectivity: `ν(k)` is
output by the end of stage `k`; no repetitions by construction.  ∎

**Corollary 6.4 (maximal runs exist).**  By Lemma 6.3 applied to `D` and
Theorem 5.7(ii) applied prefix-wise, the enumeration is an infinite run
executing every event; it is weakly fair (no event is neglected — every
event is executed).  Weak fairness is therefore satisfiable, not vacuous.

### 6.3 Fairness ⟺ completeness

**Theorem 6.5.**  For an infinite run `ρ`:
`ρ` is weakly fair  ⟺  `E_ρ = E_all` (every event is executed).

*Proof.*
(⟸)  Suppose `e` is enabled in `s_m` for all `m ≥ n`.  If `e` were
executed at some position `k`, then `e` is never enabled after position
`k` (Corollary 5.2), contradicting enabledness at `m = max(n, k) + 1`.
So `e` is never executed — contradicting `E_ρ = E_all`.  Hence no
fairness violation exists.

(⟹)  Let `ρ` be weakly fair, with states `s_k = (T_k, U_k)`.

*Step 1: every enabled event is eventually executed.*  If `e` is enabled
at `k` and never executed, stability (Corollary 3.3) makes `e` enabled at
every `m ≥ k`, a weak-fairness violation.

*Step 2: every tree is eventually in `T`.*  Structural induction on
`Tree`.  Atoms: in `T₀`.  Composite `t = pair{x,y}`, `x ≠ y`: by
induction hypothesis choose `n` with `x, y ∈ T_n` (T monotone, Lemma 2.2,
lets one `n` serve both).  Write `p := {x,y}`.  Case (a): `pair p ∈ T_n` —
done.  Case (b): `p ∈ U_n`.  Then `resolve p` is enabled at `n`; by Step
1 it is executed at some `m ≥ n`, so `pair p ∈ T_{m+1}`.  Case (c):
otherwise.  Then all four guards of `link p` hold at `n`, so `link p` is
executed at some `m` (Step 1), putting `p ∈ U_{m+1}` — case (b).

*Step 3: every event is executed.*  Let `p = {x,y} ∈ P₂`.  By Step 2 pick
`n` with `x, y ∈ T_n`.  If `pair p ∈ T_n`: `resolve p` was executed
before `n` (Lemma 2.3, T2), and its guard `p ∈ U` at that time forces a
prior `link p` (Lemma 2.3, `U₀ = ∅`) — both executed.  If `p ∈ U_n`:
`link p` was executed (Lemma 2.3), and `resolve p` is enabled, hence
executed (Step 1).  Otherwise `link p` is enabled at `n`, hence executed;
then `resolve p` becomes enabled, hence executed.  ∎

### 6.4 The limit

**Definition 6.6 (limit of an infinite run).**  For an infinite run `ρ`
with states `(T_k, U_k)` define

    T∞(ρ) := ⋃_k T_k ;

and say `U` **converges pointwise** to `U∞(ρ)` iff for every `p ∈ P₂` the
truth value of `p ∈ U_k` is eventually constant, with `U∞(ρ)` the set of
`p` for which it is eventually true.  (`T` needs no such care: membership
in `T` is monotone, so `T∞` is a plain union = pointwise limit.)

**Theorem 6.7 (all maximal runs converge to the same limit).**  For every
maximal (= weakly fair infinite) run `ρ`:

    T∞(ρ) = Tree      and      U_k → U∞(ρ) = ∅ pointwise.

Moreover, for each `p ∈ P₂`, `p ∈ U_k` holds exactly on the finite window
`pos_ρ(link p) < k ≤ pos_ρ(resolve p)`.

*Proof.*  `T∞ ⊇ Tree` is Step 2 of Theorem 6.5; `⊆` because every element
of every `T_k` is a tree.  The window claim: `p` enters `U` only at
`link p` and leaves only at `resolve p` (Lemma 2.3), each executed exactly
once (Theorem 6.5 + Corollary 5.2), and `link p <_ρ resolve p` (Theorem
5.7(i) + (g1)).  Hence membership is eventually constantly false: `U∞ =
∅`.  ∎

### 6.5 Exactly what fairness is needed — and what fails without it

**Proposition 6.8 (event sets of arbitrary infinite runs).**  The executed
sets of infinite runs are exactly the infinite downsets of `D`; the run's
limit is `T∞ = {a,b} ∪ {pair p : resolve p ∈ E_ρ}` and `U` converges
pointwise to `U∞ = {p : link p ∈ E_ρ, resolve p ∉ E_ρ}`.
*Proof.*  (⊆) Prefix sets are downsets (Theorem 5.7(i)); their union is a
downset; the limit formulas follow from Lemma 5.1 pointwise (each
membership is eventually constant: `T` by monotonicity; for `p ∈ U`, the
only two events moving it occur at most once).  (⊇) An infinite downset
of `D` is countable with finite principal downsets, so Lemma 6.3 gives an
ω-enumeration, which is a run by Theorem 5.7(ii) prefix-wise.  ∎

So **without fairness the limit claim fails**.  Concretely: let
`t* := pair{b, pair{a,b}}`, `q* := {b, pair{a,b}}`, and take
`E* := E_all ∖ {e : link q* ≤_D e}` — the complement of an upset, hence a
downset.  It is infinite (it contains all events on the chain pairs
`{a, c_k}` where `c_0 = pair{a,b}`, `c_{k+1} = pair{a, c_k}`: their
`≤_D`-downsets descend only through children of the `c_k`, never meeting
`q*`).  Any ω-run over `E*` (Lemma 6.3) never executes `resolve q*` — the
only producer of `t*` (Lemma 2.3) — so `t* ∉ T∞`; the run is infinite but
neglects `link q*`, which becomes permanently enabled once `b` and
`pair{a,b}` are present, unlinked, and unresolved.  (Beware the tempting
wrong version of this example: "all events whose endpoints avoid `t*` as a
subtree" is *not* the right set — neither endpoint of `q*` contains `t*`,
so that set wrongly includes the producer `resolve q*` itself.  The upset
complement is the correct construction.)  Fairness is *exactly* the gap
between "infinite downset" and "all of `E_all`" (Theorem 6.5).

**Remark 6.9 (weak vs strong fairness).**  Weak fairness — stated per
event, over the countably infinite alphabet — suffices, and nothing
stronger is needed, *because enabledness is stable* (Corollary 3.3): an
event, once enabled, stays enabled until executed, so "enabled infinitely
often" and "enabled continuously from some point" coincide, collapsing
strong fairness into weak fairness for this system.  In systems with
conflict (where a competing event can disable `e`) the two differ; here
they provably do not.  What is genuinely required beyond finiteness
reasoning: (i) fairness indexed by *events* (not by event-kinds: "some
link fires infinitely often" is far too weak — Proposition 6.8's
counterexample fires infinitely many links); (ii) countability of the
alphabet (T4), so that satisfying all countably many fairness constraints
simultaneously is possible (Corollary 6.4).

---

## 7. Runs = linear extensions of D; invariance of the causal order

**Theorem 7.1 (Q1, corollary form).**
(i) **Finite case.**  A finite sequence of events is a run iff its terms
are pairwise distinct, its set `F` is a finite downset of `D`, and the
sequence linearly extends `(F, ≤_D)`.  The reached state depends only on
`F` (Theorem 5.3), via the explicit formula of §5.1.
(ii) **ω-case.**  The maximal runs are exactly the order-type-ω linear
extensions ("natural labelings") of `D` itself: bijective enumerations
`e_1, e_2, …` of `E_all` with `e_i <_D e_j ⟹ i < j`.  Every finite prefix
of a maximal run is a finite run as in (i); conversely every finite run
extends to a maximal run.
(iii) **Sense of "linear extension" in the ω-case (honesty clause).**  A
general linear extension of the infinite poset `D` is any total order on
`E_all` extending `≤_D`; most of these (e.g. of order type `ω + ω`) are
*not* runs — a run is a *sequence*, so only extensions of order type ω
qualify.  The correct statement is: maximal runs ↔ ω-type linear
extensions, which exist precisely because every principal downset of `D`
is finite (Proposition 5.5 + Lemma 6.3); the identification "runs = linear
extensions of **D**" must always be read with this order-type restriction.

*Proof.*  (i) is Theorem 5.7 with Corollary 5.2.  (ii, ⊆): a maximal run
executes every event exactly once (Theorem 6.5, Corollary 5.2) — a
bijective enumeration — and its temporal order extends `<_D` (Theorem
5.7(i) prefix-wise).  (ii, ⊇): such an enumeration is a run by Theorem
5.7(ii) prefix-wise (each prefix is a finite downset containing each next
event's predecessors), and fair because it executes everything (Theorem
6.5 ⟸).  Extension of a finite run `ρ`: apply the Lemma 6.3 procedure
with the output list initialized to `ρ` (its set is a downset, Theorem
5.7(i)).  (iii) is a statement about definitions plus Lemma 6.3.  ∎

**Lemma 7.2 (swap realizability).**  If `e, f ∈ E_all` are
`≤_D`-incomparable, there is a maximal run executing `e` before `f`, and
one executing `f` before `e`.
*Proof.*  `F := ↓e ∪ (↓f ∖ {f})` is a finite downset (union of downsets;
`↓f ∖ {f}` is one since `f` is maximal in `↓f`) containing `e` but not `f`
(`f ∈ ↓e` would mean `f ≤_D e`).  Enumerate `F` compatibly (Lemma 6.2),
extend to a maximal run (Theorem 7.1(ii)); `e` occurs within the prefix
`F`, `f` after it.  Swap the roles for the other order.  ∎

**Theorem 7.3 (all maximal runs realize the same causal partial order).**
For every maximal run `ρ`:  `E_ρ = E_all`, and `<_ρ` is a linear order
extending `<_D`.  Moreover

    ⋂_{ρ maximal} <_ρ  =  <_D .

So `D` is precisely the order-content shared by all maximal runs: two
events occur in the same relative order in *every* maximal run iff they are
`D`-comparable; every incomparable pair is scheduled both ways by some pair
of runs.  Combined with Theorem 6.7 (common limit `(Tree, ∅)`) and Theorem
5.3 (states depend on sets only), this is Q1: **the run-invariant content
of the system is exactly the pair (D, its downset states); the ordering of
any particular run is a coordinate choice.**  SPEC choice C5 is thereby
discharged as a conclusion: the true-concurrency object (a conflict-free
partial order of events) is *derived* from the interleaving system, not
assumed.

*Proof.*  First two claims: Theorem 6.5 and Theorem 5.7(i).  `⊇` of the
intersection: `<_D ⊆ <_ρ` for each maximal `ρ`.  `⊆`: if `e ≠ f` are
`D`-incomparable, Lemma 7.2 gives a maximal run with `f` before `e`, so
`(e, f)` is not in the intersection; and `e <_D f` or `f <_D e` covers the
comparable non-equal pairs, whose wrong-way ordering is excluded from every
`<_ρ`.  ∎

---

## 8. Remarks

### 8.1 The initium variant (`U₀ = {{a,b}}`)

With the variant initial state `s₀' = ({a,b}, {{a,b}})`, note
`s₀' = upd_{link{a,b}}(s₀)` and `link{a,b}` is the unique event enabled in
`s₀` (Remark 5.6).  Hence the variant system's runs are exactly the pinned
system's runs with the forced first step removed: `ρ` is a run from `s₀'`
iff `link{a,b} · ρ` is a run from `s₀`.  All results transfer verbatim
with `D` replaced by `D ∖ {link{a,b}}` (still a poset; `resolve{a,b}`
becomes the unique minimum) and the state formula offset by
`link{a,b} ∈ E`.  The SPEC's "expected immaterial" is thus confirmed in
the strong form: a bijection of run-spaces shifting one forced event.

### 8.2 Swap-equivariance (choice C2 hook)

The atom swap `a ↔ b` extends to an involutive automorphism of `Tree`
(recurse through `pair`, using unorderedness), hence acts on `P₂`, on
`E_all`, on states, and on runs; it fixes `s₀`, preserves enabledness and
effects, and is an automorphism of `D` (both generator rules are stated
swap-equivariantly).  Every theorem in this file is therefore
swap-invariant — the refutation track's C2 question, for this deliverable,
has the blanket answer "all of it".

### 8.3 Relation to Q2/Q3

`D` here is an order on *events*.  The §9/§10 questions (level-2
obstruction, universal grading) concern gradings compatible with the two
event kinds — Theorem 7.3 supplies their well-posed substrate: any
grading of "the process" must be a function of `D` (equivalently of the
downset lattice), since nothing else is run-invariant.  Nothing in this
file decides Q2/Q3.

---

## 9. Classical anchors (assessment for the ledger)

### 9.1 Commutation / Newman-style rewriting — *partial fit; Newman
proper does not apply*

As an abstract reduction system (states, one-step relation
`s → upd_e(s)` for enabled `e`), the system is **non-terminating** (Lemma
6.1), so Newman's lemma (termination + local confluence ⟹ confluence) is
inapplicable *as such*.  What holds is stronger and needs no termination:
the **diamond property** for distinct co-enabled steps (Lemma 4.1), which
yields confluence directly by the classical tiling/strip argument (Church–
Rosser via strong confluence; Huet's terminology: strong confluence with
trivial residuals).  Because events execute at most once (Corollary 5.2),
the residual theory trivializes and permutation equivalence of runs
collapses to equality of executed sets — the system is what concurrency
theory calls a *deterministic, conflict-free asynchronous transition
system* (Keller-style).  Ledger verdict: cite the diamond property /
strong confluence, **not** Newman.

### 9.2 Winskel (prime) event structures without conflict — *exact fit*

`(E_all, ≤_D, # = ∅)` is a countable prime event structure with empty
conflict relation and finite causes (Proposition 5.5).  Its finite
configurations (conflict-free downsets = all downsets, since `# = ∅`) are
in bijection with reachable states (Corollary 5.8); securings (one-event-
at-a-time enumerations of configurations) are exactly the runs (Theorem
7.1); the configuration domain is the distributive lattice / coherent
domain the representation theory predicts for conflict-free structures.
This is the *precise* classical home of the result.  Two honest caveats:
(a) all machinery specific to conflict (consistency predicates, the prime
vs general distinction's hard cases) is idle here — the instantiation is
of the degenerate, conflict-free corner; (b) in Winskel's development the
event structure is usually the *given* semantics, whereas here it is
*derived* from an interleaving system (that direction — from a transition
system with a diamond property to an event structure — is the classical
"transition systems with independence / asynchronous transition systems"
unfolding, and matches SPEC C5's demand that concurrency be a conclusion).

### 9.3 Mazurkiewicz traces — *fits only degenerately; the mechanism is
different*

Mazurkiewicz trace theory takes a (usually finite) alphabet `Σ` with a
static irreflexive symmetric independence `I` and studies words modulo
commutation of adjacent independent letters; causality of a word is read
off the *dependence* relation (non-commutation).  Differences here:
(i) the alphabet is infinite (harmless); (ii) by C1 each letter occurs at
most once in any word of the run language, so occurrences = letters and
each trace class is fully described by (downset, nothing else) — the
theory's characteristic difficulties (repeated letters, occurrence
counting) are absent; (iii) **most importantly, the causal order does not
come from non-commutation**: Lemma 4.1 shows *all* distinct events
commute whenever co-enabled — dependence in this system manifests as
guarded *never-co-enabledness* (g1, g2), not as failure of commutation.
Taking `I` := `D`-incomparability makes the finite-run language
trace-closed and trace classes ↔ downsets (consistent with Theorem 5.3),
but taking `I` := "commute in all common contexts" would yield the total
relation and lose `D` entirely.  Ledger verdict: the *conclusions* match
the trace-theoretic picture; the *mechanism* (enabling-order rather than
dependence-by-non-commutation) does not; cite traces only for the
invariance format, and prefer event structures / asynchronous transition
systems for the mechanism.  Under the C1-alternative (letters repeat,
§5.5) genuine trace/occurrence machinery would become necessary.

### 9.4 Antimatroids — *fits as the poset antimatroid, in the finite
truncations*

For each `n`, the family of downsets of `D` contained in the finite
downset `D_n := {e : φ(e) ≤ n}` (φ from Proposition 5.5) is an
**antimatroid** on ground set `D_n` — precisely the *poset antimatroid* of
`(D_n, ≤_D)`: accessible (remove a `≤_D`-maximal element) and closed under
union; its basic words are the runs confined to `D_n`.  The full system is
the direct limit of these truncations (antimatroids are finite by
definition, so the global object is a limit of antimatroids rather than
one).  What does **not** fit: the extra generality of antimatroids beyond
posets.  Our feasible families are closed under *intersection* as well,
and antimatroids whose feasible sets are intersection-closed are exactly
the poset antimatroids — so none of the genuinely non-poset examples
(convex-shelling, node-search antimatroids) can arise here.  Ledger
verdict: "poset antimatroid, and provably nothing more general".

### 9.5 Adjacent anchor (recorded for Program B)

ω-type linear extensions of a countable order with finite principal
downsets are the **natural labelings** of causal-set theory; Theorem
7.1(ii) says maximal runs = natural labelings of `D`.  This is the exact
formal hook the program memo's B1 (causal-set mapping) will need; recorded
here, not developed.

---

## 10. Ledger entries (classical concepts relied on in this file)

| Internal term | Nearest classical object | Theorems imported / reproduced |
|---|---|---|
| state/event/enabled/`upd` | labelled transition system | — (definitions only) |
| Lemma 3.1 + 4.1 | diamond property / strong confluence (Keller 1976; Huet 1980); local commutation | Church–Rosser from strong confluence (tiling); Newman's lemma assessed and *not* used (no termination) |
| `D`, downsets, `T(E)/U(E)` | partially ordered set; order ideals; Birkhoff's distributive-lattice representation | downsets form a distributive lattice; ideal lattice ↔ poset |
| Theorem 5.7 / 7.1 | linear extensions; topological sorting | finite posets have linear extensions (Szpilrajn, finite case) |
| Lemma 6.3 | ω-type linear extension / natural labeling (standard in causal-set literature) | countable poset with finite principal ideals has an ω-extension (proved inline) |
| weak fairness | weak (justice) fairness, Manna–Pnueli style | fairness ⟺ completeness proved inline; stability collapses strong into weak fairness |
| §9.2 | Winskel prime event structures; configurations; securings | conflict-free ES ↔ poset; configurations = downsets; domain of configurations distributive |
| §9.3 | Mazurkiewicz trace monoid; independence/dependence alphabets | trace equivalence = equality of dependence posets (matched only degenerately) |
| §9.4 | antimatroids / greedoids (Korte–Lovász–Schrader); poset antimatroid | intersection-closed antimatroids = poset antimatroids |
| rank `φ`, T3 size | tree size; rank functions for well-foundedness | acyclicity via strictly monotone rank |
| T1, T2 | free term algebra: constructor injectivity, distinctness of constructors | proved axiom-free in `rederive/lean/Rederive/Tree.lean` |
| T4 | countability of finitely-generated term algebras | injection into finite words |

---

## 11. Proof status

Fully proved in this file (referee bar; no gaps known to the author):
Lemmas 2.1–2.5, 3.1, 4.1, 5.1, 6.1, 6.2, 6.3, 7.2; Corollaries 3.3, 5.2,
5.8, 6.4; Theorems 5.3, 5.7, 6.5, 6.7, 7.1, 7.3; Propositions 5.5, 6.8;
the C1-necessity counterexample (§5.5); the variant/swap remarks (§8.1,
§8.2).  All proofs are constructive except as noted below; the carrier
inputs T1, T2 are already machine-checked axiom-free
(`rederive/lean/Rederive/Tree.lean`); T3, T4 are structural recursions.

Flagged, not papered over:

1. **Remark 3.2**: the "effect unchanged" clause of the task is, in this
   formalization, true by definition (effects are state-independent
   updates); the nontrivial content lives in Lemmas 3.1 and 4.1.  A
   formalization with state-dependent effects would owe a real proof here;
   ours does not.
2. **Lemma 6.3** uses a fixed surjection `ν : ℕ → E_all`; constructing `ν`
   explicitly from T4's term-printing injection is routine but not spelled
   out (no choice principle is involved — the enumeration of finite words
   is explicit).
3. **Not attempted here**: Lean mechanization of §§2–7 (the deliverable is
   prose per task M1; the intended signatures align with the F-ev design
   memo's `runs_iff_linear_extensions` interface); the C1-alternative's
   occurrence-net theory (§5.5 proves only the failure of set-determinacy
   and the survival of persistence/diamond); Q2/Q3 (out of scope, §8.3).
