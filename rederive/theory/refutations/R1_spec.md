# R1 — Adversarial audit of SPEC choice points C1–C5 and the line=pair / point=tree identification

**Referee task**: break the SPEC's non-forced choices; for each construct the
strongest variant reading of `seed/ORIGIN_RAW.md` §5–§8 and decide whether
Q1 (`rederive/theory/order_invariance.md`) and Q2
(`rederive/theory/grading_obstruction.md`) survive it. Focus on **C1**.
**Independence**: only `seed/ORIGIN_RAW.md`, `rederive/SPEC.md`, and the two
deliverables were read; classical math from own knowledge.

**Verdict in one line**: I could not break the load-bearing claims. The one
claim the task singled out for suspicion — "under the C1-alternative,
Persistence and the Diamond survive verbatim" (Q1 §5.5) — is **true**, and I
re-derived the diamond for a link/resolve pair by hand under the variant.
Q1's *headline* (set-determinacy) is genuinely C1-contingent, but the author
states this openly; it is disclosed, not smuggled. Q2's obstruction is
tree-structural and survives C1 entirely. Net: **confirmed**, with one
framing caveat about C1's textual grounding.

---

## 1. C1 — the focus. Does the variant break Persistence / Diamond?

**Pinned C1**: a resolved line persists as a "joining" (`pair{x,y} ∈ T`
blocks re-`link`). The `link` guard carries the extra conjunct
`pair{x,y} ∉ T`.

**Strongest variant (C1-alternative)**: lines vanish on resolve, re-link
allowed. The `link` guard drops `pair{x,y} ∉ T` entirely:
`link{x,y}` enabled iff `x,y ∈ T`, `x ≠ y`, `{x,y} ∉ U`. Effects `upd`
unchanged.

### 1.1 Guard exclusivity survives (this is what saves the diamond)

Q1 Lemma 2.4: `link p` needs `p ∉ U`, `resolve p` needs `p ∈ U` — mutually
exclusive. The variant drops only the `pair ∉ T` conjunct and **keeps**
`{x,y} ∉ U`. So same-pair co-enabledness is still impossible under the
variant. Consequently every pair of *distinct co-enabled* events still
carries *distinct pairs* `p ≠ q` — exactly the hypothesis the Diamond proof
(Lemma 4.1) opens with. Since `upd` is unchanged, the three case computations
of Lemma 4.1 are byte-for-byte identical. **The Diamond survives.**

### 1.2 Hand recomputation of the diamond for a link/resolve pair, in the variant

I deliberately picked a state that only the *variant* admits, to stress the
re-link case (`pair p ∈ T` while `link p` fires):

    s = (T, U),  T = {a, b, (ab), (a(ab))},  U = {{a,b}}.

- `f = resolve{a,b}` (q = {a,b}): `{a,b} ∈ U` → enabled.
- `e = link{a,(ab)}` (p = {a,(ab)}): `a,(ab) ∈ T`, distinct, `{a,(ab)} ∉ U`
  → enabled in the variant **even though** `pair p = (a(ab)) ∈ T` (pinned C1
  would forbid this event; the variant is the whole point).
- `p ≠ q`. ✓

Order 1 — `e` then `f`:
    upd_e(s) = (T, {{a,b},{a,(ab)}})
    upd_f(·) : resolve{a,b} adds (ab) to T (already present), drops {a,b}
             = (T, {{a,(ab)}}).

Order 2 — `f` then `e`:
    upd_f(s) = (T, ∅)
    upd_e(·) : link{a,(ab)} enabled since {a,(ab)} ∉ ∅
             = (T, {{a,(ab)}}).

Both orders yield `(T, {{a,(ab)}})`. **Diamond holds in the variant.** ✓
Persistence (each event still enabled after the other) is visible in the same
computation: `resolve{a,b}` stays enabled after `link{a,(ab)}` (`{a,b}` still
in U), and `link{a,(ab)}` stays enabled after `resolve{a,b}` (`{a,(ab)}` never
entered U). ✓

**Verdict on the singled-out claim**: Q1 §5.5's assertion — "Persistence
(Lemma 3.1) and the Diamond (Lemma 4.1) survive verbatim (their proofs never
used the C1 conjunct except to preserve it)" — is **CONFIRMED by hand**. The
attack the task hoped would land does not.

### 1.3 What genuinely fails under the variant — and whether it is disclosed

The variant *does* break: once-only (Cor 5.2), the state formula as a
function of event *sets* (Lemma 5.1), set-determinacy / order-invariance
(Thm 5.3), and the downset bijection (Cor 5.8). Q1 §5.5 gives the exact
counterexample:

    ρ  = (link p, resolve p),          E_ρ  = {link p, resolve p}
    ρ' = (link p, resolve p, link p),  E_ρ' = {link p, resolve p}

same executed *set*, different final `U`. I checked it: with `p = {a,b}`,
after `ρ'` the third `link{a,b}` fires (variant: `a,b ∈ T`, `{a,b} ∉ U`), so
`{a,b} ∈ U` after `ρ'` but not after `ρ`. Correct. Order-invariance under
the variant can only be phrased over occurrence sequences / multisets, i.e.
one is forced from the alphabet-poset into an occurrence-net. **This is
exactly what the deliverable says.** No overclaim: Q1's headline is
explicitly conditioned on C1, and the failure mode is named. Not smuggling.

### 1.4 Is C1 actually forced? (the one soft spot)

C1 is genuinely **non-forced**. The SPEC's stated rationale leans on two
texts:

- **§3 (difference-object uniqueness)**: "(a와 b의 다름)" is *one* object;
  re-contrasting the same two gives no new move — §3 lists the only available
  moves and a duplicate is not among them. This is a **strong** argument for
  C1-pinned.
- **§5 ("lines are drawn once")**: weaker than the SPEC implies. §5's operative
  phrase is "그 점과 **이어지지 않은** 다른 점들을 잇는" — draw lines to points
  *not currently joined*. After a line resolves and is consumed (`U := U∖{p}`
  in *both* models), the two endpoints are literally "not currently joined."
  A strict-letter reading of §5 therefore **leans toward the
  C1-ALTERNATIVE**, not the pin. The monotone-outward-growth *spirit* of §5
  favors the pin, but the SPEC's phrasing "§5 lines are drawn once"
  slightly overstates §5's support.

This is a caveat, not a break: the correct load-bearing ground for C1-pinned
is §3 (object uniqueness), which is solid, and the SPEC already cites it. The
recommendation (below) is to demote the §5 half of the rationale.

### 1.5 Does Q2 survive the C1-alternative?

Yes, and more cleanly than Q1. Q2 never invokes C1 (confirmed by search: the
string "C1"/"re-link"/"occurrence" does not appear in
`grading_obstruction.md`). Its obstruction is a statement about the tree
subterm order `(Tree, ⊴)` and the first-creation dependencies it induces —
both **C1-invariant**. Under the variant, `T` still grows monotonically to
all Trees and the minimal-cause structure of each tree's *first* appearance
is unchanged; re-linking/re-resolving is idempotent on `T`. Q2's own Remark
4.4 gives the obstruction directly on `(Tree, ⊴)`, with no event machinery at
all. I verified that mirror by hand (§2 below). **Q2 survives C1 in full.**

---

## 2. Independent recomputation of the Q2 witness (Theorem 4.1 + Remark 4.4)

To ensure the level-2 obstruction is not an artifact of the pinned event
model, I recomputed both the event-level and object-level witnesses.

**Event level, `E* = link{(a(ab)), (a(b(ab)))}`.** Endpoints
`x=(a(ab))` (δ=2,λ=3), `y=(a(b(ab)))` (δ=3,λ=4), both composite. Subterms of
`y`: `{y,a,(b(ab)),b,(ab)}` — do not contain `x`; and `λ(y)=4>3=λ(x)` rules
out `y⊴x`. So `x,y` ⊴-incomparable → `E*` has **two** lower covers
`resolve{a,(ab)}`, `resolve{a,(b(ab))}` (Lemma 2.4(ii)). ✓

Two saturated ⊥-chains, each cover re-checked against Lemma 2.4:

    C₁ (len 4): link{a,b} ⋖ resolve{a,b} ⋖ link{a,(ab)} ⋖ resolve{a,(ab)} ⋖ E*
    C₂ (len 6): link{a,b} ⋖ resolve{a,b} ⋖ link{b,(ab)} ⋖ resolve{b,(ab)}
                        ⋖ link{a,(b(ab))} ⋖ resolve{a,(b(ab))} ⋖ E*

Every g1 step (`link p ⋖ resolve p`) is a cover; every `resolve c(u) ⋖
link{atom,u}` step has a single composite endpoint hence a unique lower
cover; the two terminal steps into `E*` are its two incomparable-endpoint
covers. Lengths 4 and 6 from ⊥ to the same top `E*` ⇒ **no rank function**. ✓

**Object level (Remark 4.4), C1-independent.** `t*=((a(ab))(a(b(ab))))`:

    a ⋖ (ab) ⋖ (a(ab)) ⋖ t*                       (len 3)
    a ⋖ (ab) ⋖ (b(ab)) ⋖ (a(b(ab))) ⋖ t*          (len 4)

Each `s ⋖ t` verified: child, and not a proper subterm of the sibling.
E.g. `(a(ab)) ⋖ t*`: `(a(ab))` is a child of `t*`, and it is not a subterm of
the sibling `(a(b(ab)))` (whose subterms are `a,(b(ab)),b,(ab)`). ✓ Lengths 3
and 4 to the same top ⇒ `(Tree,⊴)` non-graded, using **no event/C1 data**.
The obstruction is intrinsic to the tree order. **Q2's core is robust.**

---

## 3. The line=pair / point=tree identification

SPEC §2 pins: a line **is** `{x,y}`; the resolved point **is** the tree
`pair{x,y}`. Rationale: §8 Event 1 turns a line into a point and "nothing
else individuates the new point."

**Attack**: §8 says resolution "brings forth a **NEW** point" (새로운 점).
Under the **C1-alternative** (re-linking allowed), the same pair `{x,y}` can
be linked and resolved repeatedly; §8's "new point" read literally would make
each resolution mint a *fresh* point, not re-instantiate the fixed tree
`pair{x,y}`. That reading forces an occurrence-net carrier (a growing labelled
multiset), collapsing `T∞ = Tree` and much of Q1.

**Why it does not land**: this tension exists *only* under the
C1-alternative. Under **C1-pinned**, each pair is resolved at most once
(Cor 5.2), so "new point" and "the point is `pair{x,y}`" never collide — the
point is new *because it is created for the first and only time*. The two
pins (C1-pinned + point=tree) are **mutually reinforcing**: adopt one without
the other and the friction appears; adopt both, as the SPEC does, and the
identification is coherent. So the identification is not independently
refutable — its coherence is inherited from C1, which §1.4 already judged
well-grounded (via §3). Worth recording as: *point=tree is not a separate
free choice; it is entailed by C1-pinned + §8's "one point per line."*

---

## 4. C2–C5 (secondary; no break found)

- **C2 (atoms distinguishable / swap `a↔b`)**: Q1 §8.2 claims blanket
  swap-invariance. Checked the mechanism: both generator rules (g1),(g2) and
  the `upd` effects are stated symmetrically in the children, and `σ` is an
  involutive `Tree`-automorphism, so it acts on `P₂`, `E_all`, states, runs,
  and fixes `s₀`. Every named theorem is `σ`-equivariant. The C2-alternative
  (quotient by swap) keeps precisely the `σ`-invariant statements — which is
  all of them. No break; Q2 §6.6/6.7 even *uses* the surviving swap symmetry
  to prove non-separation. Consistent.
- **C3 (history-blind linking vs generation-locked)**: the C3-alternative is
  the lockstep/foliation reading §6 flags. Q2 §3 formalizes exactly that as
  the *stratification* (Def 3.1) and proves it **fails** at
  `ℓ*=link{(ab),(a(ab))}` (λ=5). So the C3-alternative is not a threat to be
  survived — it is the object Q2 refutes. Internally consistent.
- **C4 (self-pair forbidden)**: SPEC lists no live alternative; §3 is
  explicit ("nothing exists to distinguish x from x"). Built into the
  alphabet. Nothing to attack.
- **C5 (no simultaneity; concurrency = order-freedom)**: derived as a
  *conclusion* in Q1 Thm 7.3 (`⋂ <_ρ = <_D`), not assumed. A true-concurrency
  input would be circular; the SPEC correctly makes it output. No break.

---

## 5. Bottom line

The task's targeted attack — "if lines vanish on resolve and re-linking is
allowed, do Persistence and the Diamond fail?" — **does not succeed**: I
recomputed the diamond for a link/resolve pair in a state only the variant
admits (§1.2) and it commutes; guard exclusivity (the real load-bearing
invariant) is untouched by dropping the `pair ∉ T` conjunct (§1.1). Q1's
persistence/diamond survive the variant exactly as the deliverable claims;
its set-determinacy headline is C1-contingent but the contingency is
disclosed with a correct counterexample (§1.3). Q2's obstruction is
tree-intrinsic and survives C1 outright, verified at both event and object
level (§2). The line=pair/point=tree pin is coherent under C1-pinned and
entailed rather than free (§3). C2–C5 yield no break (§4).

**One required fix (framing, not a theorem defect)**: the SPEC's C1 rationale
cites §5 ("lines are drawn once"); a strict-letter reading of §5's
"이어지지 않은" (not *currently* joined) actually leans toward the
C1-ALTERNATIVE. C1-pinned should rest its case on **§3 (uniqueness of the
difference-object)**, which is sound; the §5 clause of the rationale should be
demoted or dropped so the pin is not defended on its weakest ground. This does
not alter any proof in Q1 or Q2.
