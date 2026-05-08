import E213.Theory.Raw
import E213.Theory.RawLevels

/-!
# Raw.Demo — bare-metal generation of Raw, ∅-axiom

How Raw is generated, level by level, with no extra structure:

```
  L0  := { a, b }                       — 2 atoms
  L1  := L0 ∪ { a/b }                   — 3 terms
  L2  := L1 ∪ { a/(a/b),  b/(a/b) }     — 5 terms
```

The generator (the only operation) is the smart constructor

```
  Raw.slash : (x y : Raw) → x ≠ y → Raw
```

with two non-negotiable properties baked into its type:

  * `x ≠ y`    — there is no `a/a`, no `b/b`        (no self-distinction)
  * canonical  — `b/a` collapses to `a/b`            (no orientation)

So `slash` is a *symmetric, irreflexive distinction*.  Everything below
follows from those two clauses + the two atoms.

Every theorem here is closed by `rfl` / `decide` / one short term;
`#print axioms` reports the empty list for each.
-/

namespace E213.Theory.Raw.Demo

open E213.Theory

-- ════════════════════════════════════════════════════════════
-- §1.  Level 0  —  the two atoms
-- ════════════════════════════════════════════════════════════

/-- The two atoms are decidably distinct. -/
theorem a_ne_b : Raw.a ≠ Raw.b := by decide

/-- |L0| = 2. -/
theorem level0_count : ([Raw.a, Raw.b] : List Raw).length = 2 := rfl


-- ════════════════════════════════════════════════════════════
-- §2.  Generator — the smart constructor `slash`
-- ════════════════════════════════════════════════════════════

/-- The unique level-1 composite. -/
def ab : Raw := Raw.slash Raw.a Raw.b a_ne_b

/-- Symmetric "between" — `slash` is independent of argument order. -/
theorem slash_ab_eq_slash_ba :
    Raw.slash Raw.a Raw.b a_ne_b
      = Raw.slash Raw.b Raw.a (Ne.symm a_ne_b) :=
  Raw.slash_comm Raw.a Raw.b a_ne_b

/-- Hence `b/a` is literally `a/b`. -/
theorem ba_collapses_to_ab :
    Raw.slash Raw.b Raw.a (Ne.symm a_ne_b) = ab :=
  (Raw.slash_comm Raw.a Raw.b a_ne_b).symm


-- ════════════════════════════════════════════════════════════
-- §3.  Level ≤ 1  —  enumeration
-- ════════════════════════════════════════════════════════════

/-- |L1| = 3   (a, b, a/b). -/
theorem level1_count : Raw.level1_set.length = 3 := Raw.level1_card

/-- All three are distinct. -/
example : Raw.level1_set.Nodup := by decide


-- ════════════════════════════════════════════════════════════
-- §4.  Level ≤ 2  —  enumeration
-- ════════════════════════════════════════════════════════════

/-- The two depth-2 newcomers, with `a/b` plugged into the right slot. -/
def aab : Raw := Raw.slash Raw.a ab (by decide)
def bab : Raw := Raw.slash Raw.b ab (by decide)

/-- |L≤2| = 5. -/
theorem level2_count :
    (Raw.level1_set ++ Raw.level2_new).length = 5 := Raw.level2_total_card

/-- All five are distinct. -/
example : (Raw.level1_set ++ Raw.level2_new).Nodup := by decide


-- ════════════════════════════════════════════════════════════
-- §5.  Depth observable
-- ════════════════════════════════════════════════════════════

theorem depth_a   : Raw.depth Raw.a  = 0 := rfl
theorem depth_b   : Raw.depth Raw.b  = 0 := rfl
theorem depth_ab  : Raw.depth ab     = 1 := rfl
theorem depth_aab : Raw.depth aab    = 2 := rfl
theorem depth_bab : Raw.depth bab    = 2 := rfl


-- ════════════════════════════════════════════════════════════
-- §6.  Leaves observable
-- ════════════════════════════════════════════════════════════

theorem leaves_a   : Raw.leaves Raw.a  = 1 := rfl
theorem leaves_b   : Raw.leaves Raw.b  = 1 := rfl
theorem leaves_ab  : Raw.leaves ab     = 2 := rfl
theorem leaves_aab : Raw.leaves aab    = 3 := rfl
theorem leaves_bab : Raw.leaves bab    = 3 := rfl


-- ════════════════════════════════════════════════════════════
-- §7.  Swap  —  the a ↔ b automorphism
-- ════════════════════════════════════════════════════════════

theorem swap_a : Raw.swap Raw.a = Raw.b := rfl
theorem swap_b : Raw.swap Raw.b = Raw.a := rfl

/-- `a/b` is a swap-fixed point: relabelling a↔b inside, then
    re-canonicalising the order, lands on the same term. -/
theorem swap_ab : Raw.swap ab = ab := by apply Subtype.ext; rfl

/-- The two depth-2 terms are swap-conjugate. -/
theorem swap_aab : Raw.swap aab = bab := by apply Subtype.ext; rfl
theorem swap_bab : Raw.swap bab = aab := by apply Subtype.ext; rfl

/-- Swap is involutive on every Raw. -/
theorem swap_swap (r : Raw) : Raw.swap (Raw.swap r) = r := Raw.swap_swap r

/-- Swap preserves `depth` — by `rfl` on every level-≤2 term. -/
theorem swap_depth_a   : (Raw.swap Raw.a).depth = Raw.depth Raw.a := rfl
theorem swap_depth_b   : (Raw.swap Raw.b).depth = Raw.depth Raw.b := rfl
theorem swap_depth_ab  : (Raw.swap ab   ).depth = Raw.depth ab    := rfl
theorem swap_depth_aab : (Raw.swap aab  ).depth = Raw.depth aab   := rfl
theorem swap_depth_bab : (Raw.swap bab  ).depth = Raw.depth bab   := rfl

/-- Swap preserves `leaves` — by `rfl` on every level-≤2 term. -/
theorem swap_leaves_a   : (Raw.swap Raw.a).leaves = Raw.leaves Raw.a := rfl
theorem swap_leaves_b   : (Raw.swap Raw.b).leaves = Raw.leaves Raw.b := rfl
theorem swap_leaves_ab  : (Raw.swap ab   ).leaves = Raw.leaves ab    := rfl
theorem swap_leaves_aab : (Raw.swap aab  ).leaves = Raw.leaves aab   := rfl
theorem swap_leaves_bab : (Raw.swap bab  ).leaves = Raw.leaves bab   := rfl

/-
The corresponding *general* statements
  `(Raw.swap r).depth  = r.depth`
  `(Raw.swap r).leaves = r.leaves`
hold for every `r : Raw` (Theory/Raw/Levels.lean), but those upstream
proofs go through `simp only`, which leaks `propext`.  Under the
∅-axiom standard (CLAUDE.md) any `propext` leak fails the purity
contract — so this demo stops at the bare-metal `rfl`-level instances
above and does not re-export the leaky generalisations.
-/

end E213.Theory.Raw.Demo


/-! ## Axiom audit — every theorem ∅-axiom (empty list expected) -/
#print axioms E213.Theory.Raw.Demo.a_ne_b
#print axioms E213.Theory.Raw.Demo.level0_count
#print axioms E213.Theory.Raw.Demo.slash_ab_eq_slash_ba
#print axioms E213.Theory.Raw.Demo.ba_collapses_to_ab
#print axioms E213.Theory.Raw.Demo.level1_count
#print axioms E213.Theory.Raw.Demo.level2_count
#print axioms E213.Theory.Raw.Demo.depth_a
#print axioms E213.Theory.Raw.Demo.depth_ab
#print axioms E213.Theory.Raw.Demo.depth_aab
#print axioms E213.Theory.Raw.Demo.leaves_ab
#print axioms E213.Theory.Raw.Demo.leaves_aab
#print axioms E213.Theory.Raw.Demo.swap_a
#print axioms E213.Theory.Raw.Demo.swap_ab
#print axioms E213.Theory.Raw.Demo.swap_aab
#print axioms E213.Theory.Raw.Demo.swap_swap
#print axioms E213.Theory.Raw.Demo.swap_depth_a
#print axioms E213.Theory.Raw.Demo.swap_depth_ab
#print axioms E213.Theory.Raw.Demo.swap_depth_aab
#print axioms E213.Theory.Raw.Demo.swap_leaves_a
#print axioms E213.Theory.Raw.Demo.swap_leaves_ab
#print axioms E213.Theory.Raw.Demo.swap_leaves_aab
