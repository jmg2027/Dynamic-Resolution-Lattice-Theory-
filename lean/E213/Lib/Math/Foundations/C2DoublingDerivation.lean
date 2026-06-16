import E213.Lib.Math.Algebra.Mobius213ModFive
import E213.Lib.Physics.Simplex.Counts

/-!
# C2DoublingDerivation — the period-ratio reading of c=2 in K_{3,2}^{(c=2)}

In the current canonical form, `c` is the **edge multiplicity / layer
count** of `K_{NS,NT}^{(c)}` (parallel edges per `(s,t)` incidence; the
third axis, orthogonal to graph shape) and `c = 2` is a **derived
presentation parameter** — set so `b_1(K_{3,2}^{(c=2)}) = 6c−4 = 8 = NS²−1`
reproduces the SU(3) adjoint.  It is NOT a forced 4th atomic primitive:
canonical status is **3 forced `(NS,NT,d)` + 1 posited `c`**
(`theory/physics/foundations/atomic_constants.md`,
`research-notes/frontiers/atomic_c_multiplicity_forcing.md`).

This file records the **period-ratio reading** of that same `c = 2`: under
the Möbius generator `P = [[2,1],[1,1]] (mod 5)`,

```
P^5  ≡ -I (mod 5)    ← pentagonal HALF-rotation (sign flip)
P^10 = (P^5)² ≡ +I (mod 5)    ← FULL closure (sign restored)
                ↑
                │
            full / half = 10 / 5 = 2   (binary cover ratio)
```

so `c = full_period / half_period = 10/5 = 2`.  The theorems below verify
this ratio and its coincidences (`= NT`, the temporal-axis cardinality;
`= (d+1)/NS`; `= |Sym 2|`) by `decide` — all PURE.

**Status of this as a *forcing* (current form).**  The period-ratio is NOT
a forcing of `c`: `half_period = 5` and `full_period = 10` are literals, and
`full/half = 2` is the trivial `(−I)² = I` (any sign-flipping half-period
gives ratio 2 — it re-expresses `|{+1,−1}| = 2`, no `P`- or `5`-specific
content).  Likewise `c = NT` is a numerical coincidence of two distinct 2's
(the temporal slot count vs the edge multiplicity), not a structural
identity — the same argument would give `c = NS = 3`.  Both routes are
analysed and refuted-as-forcing in the frontier above.

So read this file as: **the binary-cover period-ratio and the temporal
`c = NT` are two Lens readings that *present* the same atomic `2` already
fixed as the edge multiplicity** (the "anisotropy / temporal-refinement"
reading of `c`, bridged to the layer count in
`theory/essays/cohomology/c_counter_as_layer_count.md`) — not an
independent derivation that forces `c = 2`.
-/

namespace E213.Lib.Math.Foundations.C2DoublingDerivation

open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-! ## §1.  Period definitions -/

/-- Pentagonal half-period: smallest k such that P^k ≡ ±I (mod 5).
    For P = [[2,1],[1,1]], k = 5 (witnessed by `P^5 ≡ -I (mod 5)`). -/
def half_period : Nat := 5

/-- Pentagonal full-period: smallest k such that P^k ≡ +I (mod 5).
    k = 10 = 2 · 5 (witnessed by `P^10 ≡ +I (mod 5)`). -/
def full_period : Nat := 10

/-- The c-multiplicity ratio: `full_period / half_period`. -/
def c_multiplicity : Nat := full_period / half_period

/-! ## §2.  Atomic identifications -/

/-- half-period = d (= 5).  The pentagonal period equals the
    atomicity dimension. -/
theorem half_period_eq_d : half_period = d := by decide

/-- full-period = 2 · d (= 10).  The full closure doubles the
    half-period via the binary cover. -/
theorem full_period_eq_2d : full_period = 2 * d := by decide

/-- ★ c_multiplicity = 2.  The full / half ratio is exactly 2.  PURE. -/
theorem c_multiplicity_eq_2 : c_multiplicity = 2 := by decide

/-- ★ c_multiplicity = NT.  The binary cover ratio coincides with
    the bipartite T-axis cardinality.  PURE. -/
theorem c_multiplicity_eq_NT : c_multiplicity = NT := by decide

/-! ## §3.  Connection to K_{3,2}^{(c=2)} edge count

The edge count of K_{3,2}^{(c=2)} is:
  |E(K_{3,2}^{(c=2)})| = NS · NT · c = 3 · 2 · 2 = 12

which matches the K_{3,2}^{(c=2)} edge cochain space `Fin 12 → Bool`. -/

/-- The K-edge count is 12 = NS · NT · c.  PURE. -/
theorem K_edge_count_via_c :
    NS * NT * c_multiplicity = 12 := by decide

/-- Without the c=2 doubling, the bare K_{3,2} would have only
    6 = NS·NT edges.  The doubling produces 12 edges. -/
theorem K_edge_count_factorization :
    -- Bare K_{3,2}: 6 edges
    NS * NT = 6
    -- Doubled K_{3,2}^{(c=2)}: 12 = 6 · 2
    ∧ NS * NT * c_multiplicity = 12
    -- Doubling factor c = 2 = NT
    ∧ c_multiplicity = NT
    -- Same as 2 · NS · NT (alternative factoring)
    ∧ 2 * (NS * NT) = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §4.  Period verification cross-link to Mobius213ModFive

We don't re-prove `P^5 = -I (mod 5)` here (it's
`Mobius213ModFive.P_pow_5_eq_neg_I_mod_5`).  Instead, we record
the period values that the matrix-level closure justifies. -/

/-- Cross-link to `Mobius213ModFive`: the half-period 5 matches
    the matrix-entry residue level (P^5 entries 89, 55, 34 all
    ≡ ±1 or 0 mod 5). -/
theorem half_period_matrix_witness :
    -- 89 mod 5 = 4 ≡ -1 (per Mobius213ModFive.P5_11_mod_5)
    (89 : Int) % 5 = 4
    -- 55 mod 5 = 0 (off-diagonal)
    ∧ (55 : Int) % 5 = 0
    -- 34 mod 5 = 4 ≡ -1
    ∧ (34 : Int) % 5 = 4
    -- ⇒ P^5 ≡ -I (mod 5), justifying half_period = 5
    ∧ half_period = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Cross-link: the full-period 10 = 2·5 matches the matrix-level
    full closure `P^10 = (P^5)² ≡ (-I)² = +I (mod 5)`. -/
theorem full_period_matrix_witness :
    -- (-1)² = 1 (sign restoration)
    ((-1 : Int)) * (-1) = 1
    -- Full period = 10 = 2 · half_period
    ∧ full_period = 2 * half_period
    -- Doubling ratio = NT = 2
    ∧ full_period / half_period = NT := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §5.  Cross-domain readings of c=2

The atomic integer 2 appears as c, NT, Sym(2) order, ...
verifying it's the **same atomic primitive** across different
Lens readings. -/

/-- Cross-domain integer-2 readings: c = NT = Sym(2) order.
    All of these are the **same atomic 2** at the (NS, NT, d) = (3, 2, 5)
    atomic level. -/
theorem two_atomic_readings :
    -- c = pentagonal binary cover ratio
    c_multiplicity = 2
    -- = NT (bipartite T-axis)
    ∧ c_multiplicity = NT
    -- d - NS = NT (pentagon-minus-S-axis)
    ∧ d - NS = NT
    -- (d+1) / NS = NT (= 6/3 = 2)
    ∧ (d + 1) / NS = NT
    -- Order of Sym(2) = NT! = 2
    ∧ NT * 1 = 2
    -- All atomic primitives consistent
    ∧ NS = 3 ∧ NT = 2 ∧ d = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §6.  Phase capstone -/

/-- ★★ **c=2 period-ratio capstone**.

    Bundles the binary-cover period-ratio reading of `c = 2` into one
    PURE theorem:

      (a) half_period = 5 = d (pentagonal half-rotation)
      (b) full_period = 10 = 2·d (sign-restoration full closure)
      (c) c = full / half = 2 = NT (binary cover ratio)
      (d) K_{3,2}^{(c=2)} edge count: 12 = NS · NT · c
      (e) Without the doubling: only 6 = NS·NT edges (K_{3,2} bare)
      (f) Matrix-level witnesses cross-link to `Mobius213ModFive`
      (g) Cross-domain integer-2 readings (NT, Sym(2) order, ...)

    These are the period-ratio + `c = NT` Lens readings that *present*
    the edge multiplicity `c = 2`.  Per the file header (and the frontier
    `atomic_c_multiplicity_forcing.md`), they do not *force* `c`: the
    ratio is the trivial `(−I)² = I` and `c = NT` is a coincidence of two
    distinct 2's.  Canonical status is 3 forced `(NS,NT,d)` + 1 posited
    presentation parameter `c`.  PURE. -/
theorem c2_doubling_derivation_capstone :
    -- Period structure
    half_period = d
    ∧ full_period = 2 * d
    ∧ full_period = 2 * half_period
    -- Doubling ratio
    ∧ c_multiplicity = 2
    ∧ c_multiplicity = NT
    ∧ c_multiplicity = full_period / half_period
    -- K-edge count factorization
    ∧ NS * NT * c_multiplicity = 12
    ∧ NS * NT = 6  -- bare K_{3,2}
    -- Matrix-level witnesses (residues 89, 55, 34 mod 5)
    ∧ (89 : Int) % 5 = 4
    ∧ (55 : Int) % 5 = 0
    ∧ (34 : Int) % 5 = 4
    ∧ ((-1 : Int)) * (-1) = 1
    -- Atomic primitives
    ∧ NS = 3 ∧ NT = 2 ∧ d = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Foundations.C2DoublingDerivation
