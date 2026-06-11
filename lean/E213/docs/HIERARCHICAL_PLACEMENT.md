# Hierarchical Placement — umbrella conventions + layer audit

**Companion document to** `lean/E213/ARCHITECTURE.md` and
`lean/E213/docs/CONSOLIDATION_PROTOCOL.md` (R1–R11 rules).

The placement invariant of the E213 tree: **every directory has an
umbrella file** (`<DirName>.lean` importing every constituent), and
**every umbrella links the actual files in that directory**.  No
file is deferred or known-broken; every file builds clean.

The directive that established this organization (Mingu):

> 이런 식으로 E213디렉토리 밑의 모든 lean 파일들을 전부 수정 /
> Analysis가 제일 모범케이스인듯 아마도 / 그러고 나면 이제 본질적으로
> 계층적 설계에 대해서 완전하게 어느것이 어디로 들어가야하는지 모두
> 결정 가능할 것

Translation: apply the Analysis-style spec-as-code organization to
all lean files under E213/, after which the hierarchical design is
fully determined.

## 1. Umbrella coverage

Every top-level layer (`Term`, `Theory`, `Lens`, `Meta`,
`Lib/Math`, `Lib/Physics`) and every Math/Physics sub-tree
has an umbrella.  The top-level `Math.lean` / `Physics.lean`
umbrellas import topical sub-umbrellas, not files directly.
File counts per sub-tree are recomputed, not recorded here —
`lake build E213.<Layer>` per layer is the coverage check (§4).

## 2. Vertical-layer placement (mechanical)

Per `ARCHITECTURE.md` §0, every file's natural layer is mechanically
determined by its import closure.  Run `tools/layer_audit.py` to
recompute the distribution.

**Reading**: `Term/X.lean` files are at Term by both path AND
mechanical computation.  `Lib/Math/X.lean` files' mechanical layer
is distributed across {Term, Theory, Lens, Meta} — the path
encodes the *topical* axis only.  `Lib` is the horizontal topical
ring, not a rung in the vertical `{Term < Theory < Lens}` ordering
(`Meta` is ring-independent per `ARCHITECTURE.md`), so Lens-layer
files may import Lib (verified by `layer_audit.py`).

**Invariant**: no file imports a layer above its claimed level.
`tools/layer_audit.py` must report `## Violations: 0`.

## 3. Layer downgrade hints (informational)

Some files could mechanically move to a lower layer; they are not
violations, just below-claimed-cost.  These are *path locality*
decisions: e.g. `Theory/Atomicity/Alive` is mechanically Term-level
but lives under Theory/ because it groups topically with the rest
of `Atomicity/`.  Moving them down is optional.  Recompute the
current hint list with `tools/layer_audit.py`.

## 4. Spec-as-code rules (R1–R11)

| rule | description |
|---|---|
| R1  | File name = chapter title; no session-residue suffixes |
| R2  | Every dir has umbrella `<DirName>.lean` |
| R3  | Sub-namespace preservation when merging |
| R4  | Drop pure-bundle capstones; keep unique content |
| R5  | Verify all sub-tree umbrellas individually |
| R6  | Cycle prevention |
| R7  | Sub-cluster at 3+ files; sub-directory at ~30+ |
| R8  | Verify-and-clean after every merge stage |
| R9  | Iterative umbrella with broken-file exclusion |
| R10 | Nested-type-namespace caveat (doubled `X.X.*`) |
| R11 | Tactic-emitted hardcoded paths |

Full rule definitions: `CONSOLIDATION_PROTOCOL.md`.

## 5. Verification command set

```bash
cd lean
lake build E213.Term E213.Theory E213.Lens E213.Meta \
            E213.Lib.Math E213.Lib.Physics
# Each should report ✔ Built E213.<Layer>.

python3 ../tools/layer_audit.py | head -10
# Expects: ## Violations: 0
```

If both pass, the spec-as-code is complete and the placement
hierarchy is determined.
