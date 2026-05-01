# omega → omega213 migration guide

## Why

Lean's standard `omega` tactic introduces `[propext, Quot.sound]`
into every theorem that uses it.  These are part of the DRLT-allowed
Lean kernel base, but the strict-zero standard ("does not depend on
any axioms") used by physics-track capstones cannot accept them.

`omega213` (in `E213.Tactic.Omega213`) is an axiom-free replacement
for the patterns 213 actually uses.

## Empirical data point

```
theorem ex (n : Nat) (h : 1 ≤ n) : 2 * 1 ≤ 2 * n := by omega
#print axioms ex     -- depends on axioms: [propext, Quot.sound]

theorem ex (n : Nat) (h : 1 ≤ n) : 2 * 1 ≤ 2 * n := by omega213
#print axioms ex     -- does not depend on any axioms
```

## What `omega213` covers

The minimal initial implementation handles:

  1. `decide` (concrete decidable goals)
  2. `Nat.le_refl`, `Nat.zero_le`, `Nat.zero_lt_succ`
  3. `Nat.le_succ_of_le`, `Nat.lt_succ_of_le`
  4. `Nat.mul_le_mul_left`, `Nat.mul_le_mul_right`
  5. `Nat.pos_of_ne_zero`
  6. `assumption` (matching hypothesis)

## What it does NOT cover (yet)

Common patterns that `omega` handles but `omega213` doesn't, with
suggested manual replacements:

| Pattern | Replacement |
|---|---|
| `n + 1 - 1 = n` | `Nat.succ_sub_one` (rfl-true on Nat.succ) |
| `a + b = b + a` | `Nat.add_comm a b` |
| Transitivity `a ≤ b ≤ c ⊢ a ≤ c` | `Nat.le_trans h₁ h₂` |
| Subtraction with bounds | intermediate `have` with `Nat.sub_lt_succ` |
| Linear combinations | inline `Nat.add_le_add`, `Nat.mul_lt_mul_*` |

## Migration procedure

1. Identify a file with many `by omega` calls.
2. `import E213.Tactic.Omega213` and `open E213.Tactic`.
3. For each `by omega`:
   a. Try `by omega213` first.  If it builds + 0-axiom, done.
   b. Otherwise inline a specific Nat lemma: `exact Nat.foo h`.
   c. If a NEW pattern recurs ≥ 3 times, add a branch to
      `omega213` macro in `Tactic/Omega213.lean`.
4. After conversion, verify with `#print axioms <theorem>`.

## Strategy: top-down vs bottom-up

**Bottom-up (recommended)**: convert leaf files first (no
downstream dependencies), then move toward capstones.  Each file's
axiom signature becomes 0-axiom monotonically.

**Top-down**: convert capstone obligations first.  Faster initial
wins but leaves mixed signatures across the dependency tree.

The math-branch finitist closures (validation_standard_capstone,
pure_atomic_observables_capstone, alpha_em_master_capstone) already
achieve "does not depend on any axioms" by avoiding omega in their
ultimate proof step.  Migrating internal lemmas extends that
cleanliness throughout 213.

## Coverage progression

Track migration status in a per-session HANDOFF entry or a separate
`OMEGA213_STATUS.md` listing files: original omega count → remaining
omega count → 0-axiom?

## When to grow the tactic

If a file's `by omega` calls predominantly fall into a NEW pattern
that omega213 can't handle, add ONE branch to the `macro_rules` in
`Tactic/Omega213.lean` with:
  - Documentation of which Nat core lemma the branch invokes
  - A test case in the docstring showing 0-axiom verification

The tactic grows ONLY in proportion to actually-needed patterns,
never inflating beyond what 213 uses.

## Survey of current omega usage (2026-05-01)

  195 `by omega` calls across 50 files in lean/E213/

Densest clusters:
  - lean/E213/Research/Real213*.lean (cut algebra)
  - lean/E213/OS/Pigeonhole.lean (Fin index manipulation)
  - lean/E213/OS/PairForcing.lean (atomicity derivation)

Convert in dependency order: leaf files first, then mid-layer,
then capstones.  Each conversion checkpoint: lake build + #print
axioms verification on a sample of converted theorems.
