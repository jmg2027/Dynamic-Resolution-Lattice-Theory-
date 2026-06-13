# `Meta/Nat/` — ring-independent Nat helper lemmas

Pure-Nat helper lemmas that don't depend on the Theory / Lens
ring distinction.  Promoted from `Lib/Math/NatHelpers/` 2026-05-13
(Session E) — these were ring-independent and belonged in Meta.

## Files (37)

  - `PureNat.lean`         — pure-Nat building blocks
  - `UnitList.lean`        — the rung below `+`: append; `+`-commutativity
                             born as the count-shadow of unit-list append
  - `UnitGrid.lean`        — the rung-2 sibling: `×`-commutativity born
                             from the grid transpose double-count
                             (`mul_comm_from_grid`, no `Nat.mul_comm`)
  - `UnitHyper.lean`       — the rung-3 sibling: the `b`-dimensional unit
                             grid for `^`; `count = side ^ dim` positively
                             (base=length, exponent=axis count;
                             `count_eq_side_pow_dim`, no "comm lost")
  - `TwoThreeUnique.lean`  — the proven linear floor of the `^`-wall:
                             `2^a·3^b = 2^c·3^d → a=c ∧ b=d`
  - `NatDiv213.lean`       — `Nat.div` lemmas (213-internal pattern)
  - `AddMod213.lean`       — `Nat.add` mod-arithmetic
  - `MulMod213.lean`       — `Nat.mul` mod-arithmetic
  - `ModPow213.lean`       — modular exponentiation lemmas
  - `Gcd213.lean`          — GCD without Mathlib (Euclidean)
  - `IntHelpers.lean`      — Int helpers (built on Nat)
  - `Max213.lean`          — max / min combinators
  - `Beq213.lean`          — `Nat.beq` cancellation helpers
  - `BinomSymm.lean`       — binomial-coefficient symmetry
  - `EncodePair213.lean`   — injective `ℕ × ℕ → ℕ` pairing
  - `NatRing213.lean`      — ring-shaped `Nat` rearrangement lemmas
  - `PolyNat.lean`         — ∅-axiom reflection prover, univariate `Nat`
                             polynomial identities (`poly_id`)
  - `PolyNatM.lean`        — multivariate `PolyNat` reflection core
  - `PolyNatMTactic.lean`  — tactic frontend for `PolyNatM`
  - `PowBasic.lean`        — `Nat.pow` comparison toolkit, arbitrary base
                             (base-2: `Meta/Tactic/Pow213`)
  - `RootFloor.lean`       — integer `s`-th root, floor reading
                             (`rootFloor_pow` calibration; the graded
                             rate generator's probe schedule)
  - `BinTree213.lean`      — the tree floor below append: the free
                             binary magma; append = its associativity
                             quotient (`flatten`), `count` blind to
                             bracketing (`node_not_assoc`)
  - `HyperAssoc.lean`      — the wall: `+`,`×` keep assoc+comm, `^` loses
                             both (`pow_not_assoc`, `pow_not_comm`); the
                             surviving ghost `(aᵇ)ᶜ = a^(b·c)`
  - `GridReadout213.lean`  — substrate dimension + the readout split
                             (corrected: `perimeter` is an imported
                             Euclidean readout — see `Shape213`)
  - `Shape213.lean`        — the multiplicative number as a factor-LIST:
                             area = product-collapse, dimension = #factors,
                             `refine` splits a dimension fixing area;
                             **`×` = list append** (`shapeProduct_append`),
                             **`^` = list repeat** (`shapeProduct_lrepeat`) —
                             the list-form tower (dual of `count_append`)
  - `Iterate213.lean`      — the diagonal climb is iteration; the count
                             slot adds (`iter_add`) and **multiplies**
                             (`iter_mul`); `+`,`×`,`^` as `iter`; the
                             surviving ghost `(aᵇ)ᶜ=a^(b·c)` an `iter_mul`
                             instance; idempotent climb builds no tower
  - `HyperLadder.lean`     — the tower as ONE recursion: `hyperop (k+1) a b =
                             iter (hyperop k a) b (seed k a)`, so `+`,`×`,`^` =
                             `hyperop 1/2/3`; §4 the commutativity window `{1,2}`
                             (dies at `^`, both boundaries); §5 the **vertical
                             (iter-recursion) laws** that survive *every* level
                             past `^` (`hyperop_climb`/`right_one`/`arg_two`/
                             `base_one`), generic in `k`; funext-free via `iter_congr`
  - `ExpVector.lean`       — the tower's vector-linear system: numbers as
                             prime-exponent vectors with `×`=`vecAdd`,
                             `^`=`vecSmul` (`toVec_mul`/`toVec_pow`), faithful
                             (`toVec_faithful`) + finite-support; a **setoid**
                             (`vecEq`, no funext).  Flat `^` (`vp_pow_geodesic`,
                             constant increment) vs curved `↑↑` (`toVec_tetration`/
                             `vp_tetration_curved`, scalar = tower-value) = the
                             holonomy boundary.  Realises frontier D′
  - `StrictLocate213.lean` — the strict locating primitive: `a<e<a+2 →
                             e=a+1` (`locate_strict`); founding identity
                             needs strict `<`, not `≤` (which contains `=`)
  - `ListLocate213.lean`   — `locate_strict` pushed onto the list: strict
                             proper-extension order, `locate_list` (unique
                             list in a next-next gap); location works
                             because a list is linear (one tail) — branches
                             on the tree (`BinTree.node`)
  - `CoAppend213.lean`     — the co-operation dual of append: `splits` (all
                             cuts); `mem_splits_iff` — a split IS an
                             append-witness, so inverse questions are
                             co-operations, not inverse operations; co-size
                             = `length+1`
  - `Convolution213.lean`  — split-then-reglue: `conv f g n = Σ_{i+j=n}
                             f i·g j` (Cauchy/polynomial product, off the
                             `+×^` diagonal); `(1+x)²`, `(1+x)³` by `rfl`;
                             `conv_comm` (peel both ends = swap symmetry),
                             `conv_add_left` (bilinear); assoc open
  - `Valuation.lean`       — the `q`-adic valuation `vp q n` over ℕ
  - `VpMul.lean`           — the exponent-lattice engine (T3): `vp_mul`
                             (`vp p (m·n) = vp p m + vp p n`, prime `p`),
                             `vp_pow`, `vp_self_pow`, Euclid's lemma
  - `VpSeparation.lean`    — the keystone: `vp_separation`
                             (`(∀p prime, vp p m = vp p n) → m = n`) =
                             unique factorization / `exp` is a faithful
                             coordinate; `exists_prime_factor` + descent
  - `FoldCriterion.lean`   — two powers are equal iff their prime-exponent
                             readings match (`pow_eq_pow_iff_vp`); distinct
                             primes never collide (`prime_pow_unique`,
                             `2^a=3^b→a=b=0`); the fold criterion
                             (`fold_iff_collinear`)
  - `NoOrderModP.lean`     — folding the counting line into a circle
                             `1..p` (`next x = x+1`, `next p = 1`) kills
                             order: `no_wrapping_order` (irreflexive +
                             `next`-preserving + `1<2` ⟹ `False`); no `0`,
                             no `ℤ`, no `%` — contrast is the line ℕ

## Top-level

  - `Meta/Nat.lean` aggregator

## Where to add new files

  - New Nat lemma (ring-indep)   → `<name>213.lean`
  - Int helper                   → `IntHelpers.lean` (consolidate
                                    where possible)
  - Pairing / encoding           → `EncodePair213` or new
                                    `Encode<...>.lean`

## Discipline

Files in this cluster MUST be ring-independent (no Theory / Lens
/ Lib imports beyond `E213.Prelude`).  Promotion criteria:
  - Pure Nat / Int arithmetic
  - Used across multiple rings
  - No commitment to the 213 axiom set (Raw / Lens)
