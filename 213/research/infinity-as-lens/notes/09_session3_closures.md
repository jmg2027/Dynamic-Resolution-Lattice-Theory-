# 09 — Session 3 closures

Follow-up to sessions 1 and 2.  Two theorems that were
earlier deferred are now closed; one new witness added.

## Closures

### Anti-distributivity (CD session 1 deferral)

`Lipschitz.conj_mul_anti : conj (u * v) = conj v * conj u`

Now formally proved in `framework/E213/Research/CDDouble.lean`.

Approach:
- Added ZI helpers in `ZIArith.lean`: `conj_add`, `conj_sub`,
  `neg_mul`, `mul_neg`, `neg_neg`.
- Re component: rewrite chain using these + `conj_mul` +
  `conj_conj` + two `mul_comm` steps.
- Im component: descend to `ZI.ext`, two Int polynomial
  subgoals closed by `omega` after initial ZI-level
  `conj_conj` + `neg_mul`.

Mathematical content: the CD-signature reversed-order
distributivity is now formal.  Lipschitz has a complete
CD-style involution (involutive + non-identity +
anti-distributive), distinct from the Lens R4 same-order
distributivity.

### signedLens non-injectivity

New theorem in `framework/E213/Infinity/BTower.lean`:

`signedLens_not_injective : ¬ Function.Injective signedLens.view`

Witnesses:
- `signedLens_kernel_witness_pos = a / (b / (a / b))`: view
  = `1 + (-1 + 0) = 0`.
- `signedLens_kernel_witness_neg = b / (a / (a / b))`: view
  = `-1 + (1 + 0) = 0`.
- Same view but distinct as Raws (different Tree
  canonical form, verified by `decide`).

Combined with `signedLens_surjective` (session 2):
`signedLens : Raw → ℤ` is surjective but not injective —
each integer has a non-trivial fiber.  Fits the
"observation-many-to-one" picture of Lens views.

## Status

Track targets:
- Σ2 / Σ3 / Σ4 / Σ5 / Σ6 / Σ7: all formal.
- CD layer 1 (Lipschitz): structure + mul + conj +
  conj_conj + conj_ne_id + non-commutativity +
  anti-distributivity — all formal.
- signedLens: surjective + not-injective — both formal.

Still deferred:
- Lipschitz norm multiplicativity `|uv|² = |u|² · |v|²`
  (8-variable Int polynomial identity; likely beyond
  current `quad_norm`).
- CD layer 2: Cayley octonions (`CDDouble Lipschitz`).
  Needs Lipschitz `Add/Neg/Sub` supplement first, then
  same CD formula.
- CD layer 3: sedenions (where R3 finally breaks, first
  CD level with zero divisors).
- Meta-level Σ7 writeup distinguishing potential from
  completed infinity.

## Lean stats (accumulated)

- Research modules: 16 files under `E213/Research/`.
- Infinity modules: 7 files under `E213/Infinity/`.
- Meta modules: 9 files under `E213/Meta/` (including
  LensCharacterisation, ParityLens, PathLens, MaxLens,
  ZMod6Lens from session 1).
- Notes: 9 markdown files under `research/infinity-as-lens/`.
- 0 sorry, 0 axiom, Mathlib-free, `lake build` clean.
