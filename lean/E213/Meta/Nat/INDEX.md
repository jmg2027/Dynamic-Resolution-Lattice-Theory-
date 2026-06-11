# `Meta/Nat/` — ring-independent Nat helper lemmas

Pure-Nat helper lemmas that don't depend on the Theory / Lens
ring distinction.  Promoted from `Lib/Math/NatHelpers/` 2026-05-13
(Session E) — these were ring-independent and belonged in Meta.

## Files (31)

  - `PureNat.lean`         — pure-Nat building blocks
  - `UnitList.lean`        — the rung below `+`: append; `+`-commutativity
                             born as the count-shadow of unit-list append
  - `UnitGrid.lean`        — the rung-2 sibling: `×`-commutativity born
                             from the grid transpose double-count
                             (`mul_comm_from_grid`, no `Nat.mul_comm`)
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
  - `Shape213.lean`        — the internal readout is the shape (an ordered
                             factorization): area = product-collapse,
                             dimension = #factors, `refine` splits a
                             dimension fixing area; substrate dimension =
                             `exp`'s axis at coarser resolution, ONE source
  - `Iterate213.lean`      — the diagonal climb is iteration; the count
                             slot adds (`iter_add`) and **multiplies**
                             (`iter_mul`); `+`,`×`,`^` as `iter`; the
                             surviving ghost `(aᵇ)ᶜ=a^(b·c)` an `iter_mul`
                             instance; idempotent climb builds no tower
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
  - `Valuation.lean`       — the `q`-adic valuation `vp q n` over ℕ
  - `VpMul.lean`           — the exponent-lattice engine (T3): `vp_mul`
                             (`vp p (m·n) = vp p m + vp p n`, prime `p`),
                             `vp_pow`, `vp_self_pow`, Euclid's lemma

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
