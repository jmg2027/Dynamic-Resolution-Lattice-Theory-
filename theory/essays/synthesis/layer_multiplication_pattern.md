# Layer multiplication as a general pattern

A single proof shape appears in three different DRLT closures:
the c-multiplicity layers of `K_{NS, NT}^{(c)}` cohomology, the
P-iteration depth in the Lucas-Pell trace orbit, and the
Stern-Brocot mediant Vandermonde decomposition.  Each closure
starts with a fact at *one level*, replicates that fact along
an offset parameter, and proves a cancellation lemma that
absorbs the offset.  Stack the levels, count the summands —
that is the closure.

## 213-native answer

A **layer-multiplication structure** consists of three pieces:

  · An **invariant** that holds at the base level (`m = 0`,
    `k = 0`, or `(NS₁, NT₁) = (1, 1)`).
  · An **offset translation** indexing parallel copies
    (`m : Fin c`, `k : ℕ`, mediant `(NS₁ + NS₂, NT₁ + NT₂)`).
  · A **cancellation lemma** showing the offset commutes
    through the invariant.

Stack the c (or k, or split-parts) translates.  The invariant
becomes c independent copies; the cancellation lemma absorbs
the offset; the total content is `c · (base content)`.

## Three instances

### c-counter (cohomology)

**Base**: `ψ_0(cupOpp_param c (starS i 0) β) = false` for every
S-star `i` and edge cochain `β`, in
`V33EnrichedParametric`.

**Offset**: `m : Fin c` translates `starS i 0 ↦ starS i m`,
`edge_idx i' j' 0 ↦ edge_idx i' j' m`, `ψ_0 ↦ ψ_m`.  Each
shift adds `9 · m.val` to the edge index.

**Cancellation**:
`nat_decide_add_left_assoc{1,2}` (`Beq213`) shows
`(9·m + a == 9·m + b) = (a == b)`.  The `9·m` offset cancels
both sides of the equality.

**Stacked**: `parametric_arbitrary_m_full_kill_capstone` —
the kill holds at every `m : Fin c`, layer-uniform.  c
independent layer-kills span `codim ≥ c`.

### P-orbit (algebraic)

**Base**: `L(0) = NT = 2`, `L(1) = NS = 3`.  Two atomic
integers (CharPolySelf).

**Offset**: depth `k : ℕ` translates one P-iteration step.
`L(k+2) = NS · L(k+1) − det · L(k)` propagates the seed by
arithmetic.

**Cancellation**: matrix `P^(k+1) = P · P^k`.  Cayley-Hamilton
on P (`PnFibonacci`) reduces each step to a 2×2 linear
recursion — the matrix multiplication "absorbs" the depth shift.

**Stacked**: every `L(k)` is in the integer ring
`⟨{L(j) : j ≤ k}⟩_ℤ`.  Iterated for k → ω, the ring grows to
contain every mod-p period of P (`POrbitRing`,
`framework_natural_via_p_orbit_closure`).

### Mediant Vandermonde (count level)

**Base**: `binom n 0 = 1`, `binom n 1 = n`.  Pascal-level
identities (`Combinatorics/Binomial`).

**Offset**: split `n = a + b` shifts a single counter into two
copies.  `binom_succ_2 : binom (n+1) 2 = n + binom n 2`
propagates by Pascal recursion.

**Cancellation**: `move_b_to_tail` repositions a Nat in a
5-term sum, and `add_mul_pure` provides propext-free right
distribution.  Both absorb the split.

**Stacked**: `binom_add_2 : binom (a + b) 2 = binom a 2 +
binom b 2 + a · b` — three Vandermonde pieces (intra-a,
intra-b, cross-ab) from one split.  Iterated by mediant
recursion, every Stern-Brocot reachable count factors into a
finite Vandermonde sum.

## Dual function

This is not "three coincidental closures using similar
tactics."  The PROOF SHAPE is the same because the
STRUCTURAL fact is the same: a category that admits an
independent-summand decomposition into parametric pieces,
where the parameter indexes both the summands and the
offsets that connect them.

Classical reading: "induction is everywhere".  Refined:
*induction over what, in what category, with what
cancellation*.  The three closures share:

  · A **finite-index parameter** (c, k, mediant depth) over
    which summands are indexed.
  · A **base+step** form that holds at the base index.
  · A **cancellation lemma** that translates the step into a
    structural propagation, not a re-computation.

The cancellation lemma is the technical heart.  Without it,
each layer / depth / split would need its own proof.  With it,
the proof template runs once and stacks via the offset
algebra.

## Cross-frame connections

The three cancellation lemmas live at three different
infrastructure layers:

| Closure | Cancellation lemma | Layer |
|---|---|---|
| c-counter | `nat_decide_add_left_assoc{1,2}` | `Cohomology/Infrastructure/Beq213` |
| P-orbit | Cayley-Hamilton on P (`L(k+2) = NS·L(k+1) − L(k)`) | `Px/CharPolySelf`, `Px/PnFibonacci` |
| Mediant | `binom_add_2`, `add_mul_pure` | `Combinatorics/Binomial` |

Each closure picked the cancellation that matched its setting
(propext-free Nat.beq for the cohomology layer-index, matrix
recursion for the algebraic orbit, Pascal-level identity for
the combinatorial count).  Different surfaces — same shape.

The shared shape suggests a deeper structural fact: any
DRLT closure admitting a layer-multiplication structure
becomes a parametric ∀-theorem at the framework's natural
boundary.  The "natural boundary" is the index range over
which the cancellation propagates (`Fin c`, `ℕ`, Stern-Brocot
tree).  Outside that range, the closure does not hold
automatically — it needs a fresh structural argument.

## Other DRLT closures that fit the pattern

Briefly catalogued:

  · **Massey witness uniformity** at K_{3,3}^{(c)}:
    `psi_layer_rep4_eq_true_c{2..12}` — the depth-4 Massey
    witness is layer-uniform via `eta_ab_layer m, eta_cd_layer m`
    parameterised by m, decided at every c ∈ {2..12}.  Same
    layer-multiplication shape (offset cancellation in the
    Massey input cochains).
  · **Cup-image cross-layer vanishing**: `nine_block_disjoint`
    (`Beq213`) shows distinct layers occupy disjoint
    9-blocks of edge indices.  The cancellation absorbs the
    `9·m` translate; cross-layer cup vanishes structurally.
  · **Pseq Pell-Fibonacci recurrence**: every Pseq orbit step
    is a 1-step matrix multiplication; the "offset" is depth.
    Same pattern: invariant + 1-step recurrence + Cassini
    identity as cancellation.

These are not separate phenomena.  They are different surfaces
of the same closure machinery.

## Open frontier

  · **Categorical formulation**: a layer-multiplication
    structure should be a Lean typeclass capturing
    (invariant, offset, cancellation) jointly.  Concrete
    instances for `Fin c`, `ℕ`, Stern-Brocot tree should be
    Lean instances; closures would then derive from
    structural inference.  Currently each closure is proved
    independently.
  · **Sharper depth invariant**: in the P-orbit case, the
    depth function `p ↦ min { k : ord(P mod p) ∈ depth-k ring }`
    is bounded `≤ 4` empirically for `p ≤ 97`.  Asymptotic
    growth `O(log p)` is conjectured.  A typeclass-level
    "depth at which the cancellation propagates" would unify
    this with the c-counter `codim = c` and Stern-Brocot
    Vandermonde depth.

## The thing you can point at

Three Lean theorems, three different layers, one proof shape:

  · `nat_decide_add_left_assoc1` (`Beq213`) —
    `(a + b + c == a + d) = (b + c == d)`.  The cohomology
    side.
  · `binom_add_2` (`Combinatorics/Binomial`) —
    `binom (a + b) 2 = binom a 2 + binom b 2 + a · b`.  The
    combinatorial side.
  · `L_recurrence_2` (`Px/CharPolySelf`) —
    `L 2 = NS · L 1 − det · L 0`.  The algebraic side.

Each cancels an offset (additive on Nat, additive on binom
arguments, multiplicative on matrix recursion) and lets a
single proof template propagate across the parameter range.

## Cross-references

  · `theory/essays/cohomology/c_counter_as_layer_count.md` — c-counter
    reframing as layer count (instance 1)
  · `theory/essays/cohomology/disjoint_layers_as_direct_sum.md` —
    categorical direct-sum reading of the cohomology layers
  · `theory/essays/cohomology/multiplicity_layer_uniformity.md` — `9·m`
    cancellation in detail (instance 1's cancellation lemma)
  · `theory/essays/p_orbit/p_orbit_closure_master.md` — P-orbit
    closure synthesis (instance 2)
  · `theory/essays/cohomology/vandermonde_mediant_counts.md` — mediant
    Vandermonde (instance 3)
  · `theory/essays/cohomology/c_counter_programme_closure.md` — five-
    direction synthesis where the layer-multiplication pattern
    underlies Directions A/B/C and reappears in Direction E
