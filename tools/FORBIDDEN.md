# 213 Forbidden Patterns — Hook-Enforced Prohibited Code Catalog

List of code patterns automatically blocked by hooks.
Formal guard for the "DRLT Verification Criteria" defined in CLAUDE.md.

## Enforcement Mechanism

  PreToolUse  Write|Edit  → purity-guard.sh          (Tier1 + Tier2)
  PreToolUse  Write|Edit  → layer-import-guard.sh     (ring discipline)
  PreToolUse  Write|Edit  → no-legacy-narration.py    (deletion-narration / G##)
  PreToolUse  Bash         → no-amend.sh               (amend / force-push)
  PostToolUse Write|Edit  → kernel-axiom-check.sh      (Term-ring axiom regression)
  PostToolUse Write|Edit  → size-guard.sh              (CLAUDE.md ≤ 220 lines)

Configuration: `.claude/settings.json`
Scripts: `.claude/hooks/*.sh`

## Tier 1 — All lean/E213/*.lean

| Pattern | Block Reason |
|---|---|
| `^[[:space:]]*sorry\b`, `:= sorry`, `by sorry` | DRLT abandonment trigger |
| `^[[:space:]]*axiom[[:space:]]` | External axiom = theory abandonment |
| `import Mathlib` | 213-native enforced |
| `open Classical` | Constructive proofs only |
| `native_decide` | Binary trust = not a formal proof |

On violation: hook returns `block` → edit rejected.

## Tier 2 — lean/E213/Term/**/*.lean (Kernel-strict ring)

The `Term/` ring is the deep-embedded kernel: *literally 0 axiom* —
propext and Quot.sound are also not load-bearing.

| Pattern | Block Reason |
|---|---|
| `by decide` | Decidable typeclass → propext |
| `by simp`, `simp only` | Common propext path |
| `rw [...]` | Prop rewrite = propext |

Workarounds:
  - `rfl` (definitional reduction)
  - `Nat.beq` / `Nat.ble` (Bool equality/comparison)
  - `Eq.subst` with explicit motive
  - Structural induction (private helpers)
  - `Bool.cond` (if-then-else)

Example: instead of `Nat.beq_refl`, use `private theorem beq_refl' : ∀ n, Nat.beq n n
= true | 0 => rfl | n+1 => beq_refl' n` (structural induction).

## Bash hook — git safety

| Pattern | Block |
|---|---|
| `git commit --amend` | "Never amend" |
| `git push --force` / `-f` | Force-push blocked |

## Kernel axiom regression (PostToolUse)

Runs automatically after `Term/` (kernel ring) file changes:
  1. Call `tools/kernel_regress.sh` (targets `E213.Term.*`)
  2. `lake build --rehash` → `#print axioms` output
  3. If any Term-ring theorem depends on an axiom → block

Silent on success. On failure: prints violating theorem + axiom list.

## Manual Verification

  ./tools/kernel_regress.sh        # immediate check
  python3 tools/audit_axioms.py    # detailed classification
  python3 tools/port_candidates.py # unported candidates

## One Line

> "Only theorems that close under definition + Lean kernel reduction —
>  without knowing any physics or mathematics — are permitted."
