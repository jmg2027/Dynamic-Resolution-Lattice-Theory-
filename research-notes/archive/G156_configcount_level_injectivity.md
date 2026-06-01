# G156 — The fractal-level tower is a strict order-embedding

**Tier-1 scratch.**  Records a small ∅-axiom result added to
`Lib/Math/Cohomology/Fractal/ConfigCount.lean` and what it contributes to
the open question left by the N_U removal
(`research-notes/RERESEARCH_n_u_removal.md`).

## The object

`configCountD d n = d^(d^n)` — the count-Lens readout of level-`n`,
base-`d` configurations.  Parametric in both arguments; `Theory.Atomicity
.Five` selects `d = 5`, **nothing selects a level** `n`.  After the N_U
removal this is bare combinatorics: no level wears the "universe number"
crown.

## What was proven

Before this session the level direction carried only non-strict
monotonicity (`configCountD_mono_n`, `≤`).  Non-strict `≤` is compatible
with two distinct levels reading the *same* count — a plateau would let a
count-based argument quietly privilege the plateau's level.  Three new
theorems close that gap (all PURE, scan `23 pure / 0 dirty`):

  - `configCountD_strictMono_succ (d n) (hd : 2 ≤ d)` —
    `configCountD d n < configCountD d (n+1)`.  Each level is *strictly*
    more populated than the one below.  Engine: `configCountD_succ` rewrites
    level-up as `b ↦ b^d`, and the private `lt_self_pow_pure` gives
    `b < b^d` for `b, d ≥ 2` via the pure chain
    `b < b + b = 2·b ≤ b·b = b² ≤ b^d`.  The base bound
    `2 ≤ configCountD d n` (private `two_le_configCountD`) holds because
    `d^(d^n) ≥ d^1 = d ≥ 2`.
  - `configCountD_strictMono (d) (hd : 2 ≤ d)` —
    `m < n → configCountD d m < configCountD d n` (single steps chained by
    `Nat.lt_trans`).
  - `configCountD_injective (d) (hd : 2 ≤ d)` —
    `configCountD d m = configCountD d n → m = n`.  Trichotomy against
    strict monotonicity.

## 213 reading — "no level privileged" is now a theorem

`CLAUDE.md` and the RERESEARCH registry assert *no level is privileged*.
Injectivity is the structural content of that slogan, in two directions:

  1. **No two levels collapse.**  The map `n ↦ configCountD d n` is an
     injection ℕ ↪ ℕ (in fact a strict order-embedding for `d ≥ 2`).  The
     level index is *recoverable from the count alone*: the count is a
     faithful coordinate on the tower, so no count-coincidence could ever
     fuse two levels into one privileged readout.
  2. **No level is fixed/selected.**  Strict monotonicity means the tower
     has no fixed point and no plateau — there is no `n` the family
     "settles on", nothing internal to the count direction that singles
     out a level.  The only selection in the whole object is the *base*
     `d = 5` (via atomicity); the *level* axis remains a free Lens
     parameter, exactly as the RERESEARCH note claims.

So the open RERESEARCH question — *"is there a non-arbitrary selected
level, or is it purely parametric?"* — gets a partial, structural answer
on the level axis: **purely parametric, and provably so.**  The count
direction is a faithful, monotone, fixed-point-free coordinate; it offers
no handle by which to crown a level.  (The base direction is the dual
story: `Theory.Atomicity.Five` *does* select `d = 5`; that asymmetry —
base selected, level free — is itself the residue of the N_U removal.)

## What this does NOT settle

  - It does not supply the "proper 213-native concept" the originator
    deferred.  It constrains any such concept: it cannot be a *selected
    level*, since the level axis is provably structureless under the count.
  - `d = 0, 1` are excluded (the `2 ≤ d` hypothesis): `d = 1` gives the
    constant tower `1`, `d = 0` the eventually-constant `0^… `.  The
    strict story is a property of genuine branching (`d ≥ 2`), which the
    atomic base `d = 5` satisfies.

## Pointers

  - Lean: `Lib/Math/Cohomology/Fractal/ConfigCount.lean`
    (`configCountD_strictMono{_succ}`, `configCountD_injective`).
  - Open concept: `research-notes/RERESEARCH_n_u_removal.md` "OPEN concept".
  - Base selection (the dual axis): `Theory.Atomicity.Five.atomic_iff_five`.
