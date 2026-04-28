# Lean Kernel-`decide` Lessons — DRLT 213

Patterns and anti-patterns from closing universal cohomology
theorems (Universal δ²=0, Cup AW Leibniz) under the
≤ {propext, Quot.sound} standard, no `native_decide`, no Mathlib.

---

## 1. Kernel `decide` does not scale combinatorially.

327k cases OOM regardless of slicing. All of these failed the same way:

| Strategy | Cases | Result |
|---|---|---|
| `∀ a0..b9 : Bool, decide` (one giant) | 327,680 | 7+ GB → OOM |
| `cases a0 <;> ... <;> cases a4 <;> decide` | 32 × 10,240 | OOM |
| `cases a0 <;> ... <;> cases b9 <;> decide` | 32,768 × 10 | impractical |
| `List.all` Bool enumeration via `cochainAt` | 327,680 | maxRecDepth, then OOM |

**The proof term grows with case count, not with how cases are nested.**
Splitting saves nothing if total work is the same.

## 2. Algebraic lens > enumeration.

Bilinearity + linearity + decomposition reduces case count
*exponentially*, not linearly:

```
(5,1,2) Leibniz: 327,680 → 3,200 cases  (~100×)
```

Pipeline:
1. Universal bilinearity `cupAW (α + α') β = cupAW α β + cupAW α' β`
2. Universal linearity `δ(σ + τ) = δσ + δτ` (foldl induction)
3. Decompose `β = Σ_k (β k) ? e_k : 0`
4. Bilinearity expansion → per-component basis Leibniz
5. Residual XOR rearrangement closed by `List.foldr` induction

## 3. Axiom dependencies — `propext` vs `Quot.sound`.

Pure case analysis on Bool + funext + induction stays at `[propext]`.
The moment you `decide` on a finite Bool enumeration, `Quot.sound`
enters.

| Tactic | Axioms |
|---|---|
| `cases a <;> rfl` (closed Bool) | none |
| `funext + cases + rfl` | `propext` |
| `decide` on finite ∀ Bool | `propext, Quot.sound` |
| `native_decide` | adds `Lean.ofReduceBool` (BANNED) |

## 4. Definitional reduction shape > logical equivalence.

Choose encodings that reduce by `rfl`, not by `simp`.

**Bad** (needs `simp`):
```lean
def bz (β : Cochain n k) (i : Fin N) : Cochain n k :=
  if β i then basis n k i else Cochain.zero n k
```

**Good** (off-diagonal definitionally `false`):
```lean
def bz (β : Cochain n k) (i : Fin N) : Cochain n k := fun j =>
  (i.val == j.val) && β i
```

Why: `false && X = false` is the false branch of Bool's `match`,
hence definitional. The `if-then-else` form is logically equivalent
but stuck on `Decidable` elaboration.

`Cochain 5 2` decomposition collapsed from 1024 cases per j down
to 1 case (just on the diagonal value) once we switched to `&&`.

## 5. Function-level vs value-level lemmas.

Both are needed; one does not substitute the other.

```lean
-- Value-level: rewrites a leaf at fixed τ_idx
theorem cupAW_add_right (n a b : Nat) (α : Cochain n a)
    (β β' : Cochain n b) (τ_idx : Fin (binom n (a + b - 1))) :
    cupAW n a b α (Cochain.add β β') τ_idx
      = xor (cupAW n a b α β τ_idx) (cupAW n a b α β' τ_idx)

-- Function-level: rewrites *inside* a delta or another cupAW
theorem cupAW_add_right_eq (n a b : Nat) (α : Cochain n a)
    (β β' : Cochain n b) :
    cupAW n a b α (Cochain.add β β')
      = Cochain.add (cupAW n a b α β) (cupAW n a b α β')
```

Deriving function-level from value-level is one `funext` line; do it
upfront for any structural lemma you'll use inside a delta/cupAW.

## 6. Bool asymmetry trips proofs.

`Bool.and a b := match a with | true => b | false => false`
`Bool.xor a b := match a with | true => !b | false => b`

| Form | Reduces? |
|---|---|
| `false && X` | yes (definitional, false branch) |
| `false ^^ X` | yes (definitional, false branch) |
| `X && false` | no (needs `cases X` or `Bool.and_false`) |
| `X ^^ false` | no (needs `cases X` or `Bool.xor_false_right`) |

Put symbolic argument on the right when possible.

## 7. `show` parsing is subtle with infix.

```lean
show a && b = c          -- parses as: a && (b = c)  ← Bool && Prop
show ((a && b) = c)      -- correct
```

Add explicit parens around `=` arguments when Bool/Prop mix.

## 8. `List.foldr` induction = right abstraction for finite XOR facts.

Don't write 20-Bool `cases`-and-`rfl` (2²⁰ = 1M leaves, OOM).
Generalise over `List (Bool × Bool)` and induct:

```lean
theorem foldr_xor_pair (xs : List (Bool × Bool)) (a b : Bool) :
    xs.foldr (fun p acc => xor (xor p.1 p.2) acc) (xor a b)
      = xor (xs.foldr (fun p acc => xor p.1 acc) a)
            (xs.foldr (fun p acc => xor p.2 acc) b) := by
  induction xs generalizing a b with
  | nil => rfl
  | cons hd tl ih => rw [ih a b]; cases hd.1 <;> cases hd.2 <;> ...
```

Strict 0-axiom. Specialise to N-pair tuple via `List.foldr` unfolding.
Induction step is a 4-Bool decide (16 cases) — that's all you need.

## 9. `decide` OOM is not "the proposition is wrong".

Distinguish:
- **OOM during decide**: kernel can't materialise proof term in
  available memory. Goal IS true. Switch *strategy*, not the goal.
- **decide returns `False`**: proposition is actually false. See
  `LeibnizFinding.lean` — original cup product violated Leibniz,
  surfaced by decide. Different failure mode.

## 10. Encoding bijections (Cochain ↔ Fin 2^N) don't shrink work.

`encode : Cochain n k → Fin 2^N` lets you turn `∀ σ` into `∀ i ∈ Fin 2^N`.

**Same case count.** Useful for indexing/Bool-level `List.all`,
but no algebraic compression.

Only structural reductions (bilinearity, basis decomposition)
actually reduce work.

## 11. Honest negative findings drive discovery.

`LeibnizFinding.lean` documented that the original `cup` violated
Leibniz universally. That negative result led to discovering the
missing Alexander–Whitney overlap, and `cupAW` was built with the
correct convention.

Document failures. They open the next move.

## 12. 80-line file cap forces good modularity.

The (5,1,2) closure ended up split as:

```
CupAWBilinear.lean       — bilinearity (value-level)
CupAWBilinearFunc.lean   — bilinearity (function-level)
DeltaLinear.lean         — delta linearity
CupAWZero.lean           — zero structural lemmas
CupAWBasisLeibniz.lean   — basis-pair Leibniz (decide)
Cochain5Decomp.lean      — Cochain 5 1 decomposition
Cochain5_2Decomp.lean    — Cochain 5 2 decomposition
XorPairCombine.lean      — generic foldr-XOR identity
CupAWLeibnizAlgLift.lean — bilinearity-driven framework
CupAWLeibniz12Final.lean — full ∀ α β assembly
```

Each piece reusable independently.

---

## Meta-lesson

When the kernel can't brute-force, the answer is **more abstraction,
not more compute.**

The bilinearity infrastructure cost ~5 small files of universal
lemmas. Each unlocked a class of theorems previously out of kernel
reach. Upfront investment paid back ~100× on (5,1,2) alone, and is
reusable for (5,2,1), (5,2,2), and beyond.

---

## Quick-reference: when to use which strategy

| Universe size | Strategy |
|---|---|
| ≤ ~10k cases | Direct `decide`, `set_option maxHeartbeats 16000000` |
| ~10k–100k cases | Pattern enumeration via funext + decide |
| ~100k+ cases | Algebraic lift: bilinearity + linearity + basis + structural rearrangement |
| Universal over `n, k` | Structural proof: funext + cases + induction |
| `List.foldl`/`foldr` over Bool | Generic foldr lemma + induction (0-axiom) |
