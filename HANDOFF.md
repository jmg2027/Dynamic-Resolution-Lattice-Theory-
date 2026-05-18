# Session Handoff — 2026-05-18 (Lens Emergence Path review + D + E)

## Branch
`claude/review-lens-emergence-path-ZtS3A` — pushed.
Latest: `8f82d12b Theory.Raw.Congruence + Lens.Congruence: Option E
— internal Eqv + Lens bridge`.  Eight commits since branch start.

## What This Branch Did

A review-and-extend pass on the **lens emergence path** research note
(`research-notes/2026-05-18_lens_emergence_path.md`) the user wrote
earlier on the prior `claude/move-tree-to-term-ring-DDom7` branch.
The review surfaced four substantive issues; addressing them led
naturally into Step 1 (framing + new seed chapter), Step 2
(Option B — Raw-subtype carrier with closed-Raw arithmetic), plus
the minimal substrates for Options D (chart-explicit) and E
(internal congruence) from §5 of the roadmap.

Option C Phase 2+ is **deliberately skipped**: as defined in §5 it
deletes Raw-side arithmetic that Option B depends on; the two are
alternatives, not stackable.  See "Open Problems" below.

### Commit timeline

| # | Commit | Scope |
|---|---|---|
| 1 | `b5c829cc` | Research note: KO → EN translation + 4 substantive fixes |
| 2 | `da32eb66` | seed/AXIOM/09_chart_relativity.md + Nat213.{Raw,Peano} framing docstrings |
| 3 | `4ca45d25` | Nat213.Chain — Raw-subtype carrier (Option B core) |
| 4 | `7ee3890d` | Nat213.Chain — add/mul closure (without homomorphism) |
| 5 | `23ef67ea` | Nat213.Chain — omega-free toNat homomorphism, Option B complete |
| 6 | `baf8313e` | HANDOFF.md (initial post-B) |
| 7 | `2f9dd195` | Nat213.ChartGeneral — Option D (chart-parameterised chain) |
| 8 | `8f82d12b` | Theory.Raw.Congruence + Lens.Congruence — Option E (internal Eqv + lens bridge) |

### Commit 1 detail — research note hardening (`b5c829cc`)

The user-authored draft was 350 lines of Korean.  Issues caught:

1. **CLAUDE.md violation** — `.md` files must be English (verbatim
   KO quotes OK with EN translation alongside).  Translated, with
   3 user-note paragraphs kept as KO + EN pairs.
2. **§2.6 conjectural claim** — `ℕ₊ = Raw / (a ≡ b ∧
   slash_assoc)` was asserted as if obvious.  `grep` confirmed
   `slash_comm` exists (`Theory/Raw/Slash.lean:32`) but
   `slash_assoc` does **not** — flagged the candidate congruence as
   conjectural, not derivable from current axioms.
3. **§3.3 Cauchy/ℝ** — claimed "ℝ emerges via Cauchy sequence"
   without flagging `seed/RESOLUTION_LIMIT_SPEC.md` §1's structural
   inequality preservation.  Added inline caveat: under ∅-axiom,
   `limit ≠ exact value` (no `propext`, no `Quot.sound`); Real213
   marathon operates on the *trajectory side*.
4. **§0 + §7 status honesty** — "단상 / 반영 전 고찰" claimed, but
   commit list already included `ced56bef Nat213/Core.lean (Phase 1
   of C refactor)`.  Phase 1 was already taken; recommendation
   marked as partly post-hoc.

### Commit 2 detail — Step 1 framing (`da32eb66`)

- **`seed/AXIOM/09_chart_relativity.md`** (103 lines, new chapter):
  §9.1 Raw.a/Raw.b chart-local labels, §9.2 operation/object
  non-separation, §9.3 flat ontology (strict ∅-axiom reading via
  `Rawⁿ → Bool`, not `Set Rawⁿ`), §9.4 syntactic internalization
  flagged conjectural.  Cross-refs to RESOLUTION_LIMIT_SPEC,
  04_falsifiability §5.2.1, 07_self_reference §8.1.
- **`seed/AXIOM/INDEX.md`** — slot 09 row added; the historical
  `09_audit.md` (now in `lean/E213/AUDIT.md`) is distinguished from
  the new chart-relativity chapter.
- **`Nat213/Raw.lean` + `Nat213/Peano.lean`** — one-paragraph
  Framing block in each docstring pointing at seed/AXIOM/09 + the
  research note.  Raw.lean framed as Method A under `Lens.leaves`;
  Peano.lean framed as ergonomic parallel (not lens-derived), with
  iso witnessed by `.Bridge`.

### Commits 3-5 detail — Step 2 (Option B): `Nat213.Chain`

A **Raw-subtype carrier** `{ r : Raw // IsMethodAChain r }`,
parallel to (and complementing) the existing **Nat-subtype**
`Nat213.Core.Nat213 := { n : Nat // 1 ≤ n }`.  Built additively —
the existing `Nat213.Raw` arithmetic and `Nat213.Peano` inductive
type are untouched.

```
IsMethodAChain r := ∃ n : Nat, r = Raw.numeral n     -- predicate
structure Chain where val : Raw; property : IsMethodAChain val
```

**21 strict ∅-axiom symbols** (`#print axioms` returns
`does not depend on any axioms`):

| Namespace | Symbols |
|---|---|
| `IsMethodAChain.*` | `one`, `step`, `add`, `mul` |
| `Raw.value_*_chain` | `value_add_chain`, `value_mul_chain` |
| `Chain.*` (carrier + ops) | `numeral`, `one`, `val_one`, `succ`, `val_succ`, `add`, `val_add`, `mul`, `val_mul` |
| `Chain.*` (Nat bridge) | `toNat`, `toNat_numeral`, `toNat_one`, `toNat_succ`, `toNat_add`, `toNat_mul` |

**Key non-trivial choice** — *omega-free* proofs.  Initial attempt
(commit 4 + earlier draft) used `omega` for Nat arithmetic.
`tools/scan_axioms.py` flagged `propext, Quot.sound` dependence
from `omega`'s implementation, violating the ∅-axiom contract.
Commit 5 reproved the homomorphism using only Lean 4 core
lemmas: `Nat.add_comm`, `Nat.add_right_comm`, `Nat.succ_mul`,
`Nat.one_mul`.

**Naming gotcha discovered** — Lean 4's auto-generated structure
constructor `Chain.mk : Raw → IsMethodAChain val → Chain` shadows
a custom `def Chain.mk (n : Nat) : Chain`.  Renamed to
`Chain.numeral` (avoids the clash; matches `Raw.numeral` in the
sibling file).

## Verification State

```
lake build (all new files)                  ✔ clean
tools/scan_axioms.py + manual probe         ✔ 29 strict ∅-axiom symbols across this branch:
  Chain.lean                                  15 PURE / 0 DIRTY
  Chain parent-namespace                       6 PURE / 0 DIRTY
    (IsMethodAChain.{one,step,add,mul},
     Raw.value_{add,mul}_chain)
  ChartGeneral.lean                            4 PURE / 0 DIRTY
  Theory.Raw.Congruence (manual probe)         2 PURE / 0 DIRTY
    (Eqv inductive, Eqv.induction')
  Lens.Congruence.lean                         2 PURE / 0 DIRTY
    (view_eq_of_Eqv, Eqv_of_view_eq)
```

No downstream consumers broken — every new file is purely additive.

## Open Problems / Next Candidates

In priority order; the user can pick any:

### 1. Option C Phase 2+ (multi-file refactor; tension with Option B)
Per research note §7 Step 3 and §5 Option C.  Delete ad-hoc
arithmetic from `Nat213.Raw.lean` (`add, mul, addAux, mulAux,
numeral, succ`) — move all arithmetic to the codomain side or to
`Chain.lean`.  Rewrite `Bridge.lean`, audit `Tower/*` and
`Lib/Physics` for downstream impact.  **Large**: 9+ files affected.
**Conflict**: as defined, Option C deletes the Raw-side arithmetic
that Option B's `Chain.lean` depends on.  Pursuing C requires
either (i) reworking Chain.lean to use external-Nat arithmetic
(undoing B's "closed-Raw" point), or (ii) keeping a thin private
arithmetic layer in `Raw.lean` solely for `Chain.lean`'s use.
Decision needed before starting.

### 2. Option D full chart-invariance theorem
The `ChartGeneral.lean` from this branch provides only the
parameterised definition + default-chart specialisation.  Missing:
a chart-invariance theorem such as
`value (chartChain r₀ r' h n) = value r₀ + n * value r'`.
Requires a `chartChain r₀ r' h n ≠ r'` chain invariant whose proof
depends on properties of `r'` (atomicity, leaves count) — the
default chart's invariant uses `Raw.numeral_ne_b` which is
specific.

### 3. Option E specific generator instantiations
The `Theory.Raw.Congruence` from this branch provides only generic
`Eqv` + induction.  Missing: concrete generator sets that *do* sit
within the 213 axiom set.  Candidates: `Lens.leaves`-induced
generators (atoms collapse + slash-congruence), `Lens.depth`-induced
generators, etc.  Stronger §2.6 conjectures involving
`slash_assoc` remain blocked by the missing associativity proof.

### 4. §2.7 syntactic internalization (L2 prototype)
Per research note §6 question 6.  Minimal glyph → Raw mapping in
Lean.  Would give first formal evidence on whether the §9.4 cascade
halts at the resolution limit.

### 5. Smaller hygiene
- `Nat213/Raw.lean` docstring is still Korean (pre-existing, not
  Chain.lean's scope).  Translate per the same CLAUDE.md rule.
- `Nat213/Peano.lean` docstring is mostly English already.
- INDEX.md for the three new files (ChartGeneral, Congruence x2)
  — add entries to relevant indices.

## Unresolved from This Session

- **`omega` cost**: Confirmed `omega` brings `propext + Quot.sound`,
  so it cannot appear in any PURE proof.  Workaround applied
  successfully here using manual Nat lemmas; pattern is reusable
  for any future Nat-arithmetic-heavy proof.
- **Pre-existing KO docstrings in `Nat213/Raw.lean`**: noted but
  not translated — out of scope for this branch.
- **Option C vs Option B tension** documented above; not resolved
  this session.
- **Full chart-invariance (D) and concrete generator sets (E)**
  deferred — see Open Problems #2 and #3.

## File Map

```
research-notes/2026-05-18_lens_emergence_path.md     ← KO → EN + 4 substantive fixes (commit 1)
seed/AXIOM/09_chart_relativity.md                    ← NEW: chart-relativity chapter (commit 2)
seed/AXIOM/INDEX.md                                  ← slot 09 row + deprecated-09 disambiguation (commit 2)
lean/E213/Lens/Number/Nat213/Raw.lean                ← +Framing docstring block (commit 2)
lean/E213/Lens/Number/Nat213/Peano.lean              ← +Framing docstring block (commit 2)
lean/E213/Lens/Number/Nat213/INDEX.md                ← Chain.lean entry (commit 3)
lean/E213/Lens/Number/Nat213/Chain.lean              ← NEW: Raw-subtype ℕ₊ + closure + homomorphism (commits 3-5)
lean/E213/Lens/Number/Nat213/ChartGeneral.lean       ← NEW: Option D — parameterised chart (commit 7)
lean/E213/Theory/Raw/Congruence.lean                 ← NEW: Option E — generic Eqv inductive type (commit 8)
lean/E213/Lens/Congruence.lean                       ← NEW: Option E — Lens.equiv ↔ Eqv bridge (commit 8)
```

## Anchor docs (next session start)

- `CLAUDE.md` (top) — boot sequence
- `seed/AXIOM/07_self_reference.md` §8.4 — dichotomy guide
- `seed/AXIOM/09_chart_relativity.md` — the new chapter
- `research-notes/2026-05-18_lens_emergence_path.md` — long-form
  discussion
- `lean/E213/Lens/Number/Nat213/Chain.lean` — Option B end state
- `lean/E213/Lens/Number/Nat213/ChartGeneral.lean` — Option D
  minimal substrate
- `lean/E213/Theory/Raw/Congruence.lean` + `lean/E213/Lens/
  Congruence.lean` — Option E minimal substrate
