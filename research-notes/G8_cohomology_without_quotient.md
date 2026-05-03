# G8 — Cohomology Without Quotient: ∂²=0 as Theorem, Full Data Recording

**Author:** Mingu Jeong (insight); Claude (formalization)
**Date:** 2026-05-XX (this session, after G7)
**Companion Lean file:** `lean/E213/Math/Cohomology/HodgeConjecture/Bridge/CohomologyWithoutQuotient.lean`

## §0  The observation

From this session, Mingu's question:

> 코호몰로지 체인을 잡을때에도 사실 213입장에선 무슨 공리가 아니라 그냥
> 그려진 모습에서 각 차원의 코뭐시기들의 정보들을 작성하구, 사실 경계의
> 경계는 상위차원의 클로즈드 루프자나. 그렇게 정의하는게 더 계산도 정확하고
> 정의도 정확하고 의미도 와닿고 억지공리도 안붙여도되고 본질을 더 잘
> 보여주고 심지어 대수학으로 계산할수있는데. 모든 정보를 담아도 무한 항으로
> 발산을 안하니깐.

Translation:

> When picking a cohomology chain, from 213's view it's not an *axiom*
> — you just write down each dimension's co-things' information from
> the drawn picture.  Actually, "boundary of boundary" is a *closed
> loop in higher dimension*.  Defining it that way is computationally
> more accurate, definitionally more accurate, more meaningful, with
> no forced axioms, shows the essence better, and is even algebraically
> computable.  Even storing ALL the information doesn't diverge to
> infinite terms.

## §1  Standard cohomology's three sins

### Sin 1: ∂²=0 stated as defining axiom

In ZFC-flavored algebraic topology / category theory, a **chain
complex** is a sequence of abelian groups + maps satisfying
∂²=0 *as a defining condition*:

```
class CochainComplex where
  C  : ℕ → AbelianGroup
  ∂  : Π n, C n → C (n+1)
  -- AXIOM: every composition is zero
  d_squared : ∀ n, ∂(n+1) ∘ ∂(n) = 0
```

This makes ∂²=0 a *postulate*, as if without it the structure could
fail.  But geometrically, ∂²=0 is *forced* by the simplicial
combinatorics — every face of a face cancels with another face of
a face by the alternating signs.  The "axiom" is a label for what
the geometry already does.

### Sin 2: cohomology defined as quotient (information loss)

```
H^k := ker(∂_k) / im(∂_{k-1})
```

This *quotient* throws away "which cocycle representative we held".
Two representatives in the same coset are declared "equal"; the
distinction is destroyed.  In ZFC this is a feature ("we only care
about the equivalence class"); in 213 it is information loss.

### Sin 3: chain complexes lift to ∞-categories (more axiom layers)

In modern formulations (∞-categories, ∞-operads, A∞-algebras),
∂² fails to be strictly zero but holds *up to higher coherence*.
This LITERALLY records the closed-loop structure Mingu describes —
the "boundary of boundary" is a 2-morphism, not just 0.  But
formalizing this correctly requires *another* infinite tower of
axioms, each piece of which is a coherence condition.

213 sidesteps the entire tower: ∂²=0 is a `decide`-checkable theorem
on every concrete cochain, and the closure pattern is recorded
directly as Bool data.

## §2  213's reformulation

The same K_5² complex, but recorded honestly:

```lean
-- 213 cochain complex on K_5² (no axioms)
def Cochain (n k : Nat) : Type := Fin (binom n k) → Bool

def delta0 (σ : Spin) : Coupling := ...   -- explicit XOR
def delta1 (J : Coupling) : TriCochain := ... -- explicit XOR

theorem delta_sq_zero (σ : Spin) : cocycleObstruction (delta0 σ) = 0
  := by decide   -- THEOREM, not axiom
```

The Lean kernel verifies ∂²=0 by direct evaluation.  No axiom is
imposed; the geometry is just *true* of the explicit definitions.

For information preservation: every cochain is recorded as an
*explicit Bool function on a finite domain* — never quotiented,
never abstracted.  When two cochains are cohomologous, both are
preserved as data; the *fact* that they differ by a coboundary is
itself a piece of recorded data (a Bool function on the difference).

## §3  The "boundary of boundary" interpretation

Mingu's "closed loop in higher dimension":

For σ_v0 = vertex-0 indicator on K_5:
  · δ_0 σ_v0 = T at edges (0,1), (0,2), (0,3), (0,4) (star at v_0)
  · δ_1 (δ_0 σ_v0) on each K_5 triangle:
    - Triangle T_{0jk} (containing v_0): 2 of 3 edges activated, XOR = F
    - Triangle T_{jkl} (not containing v_0): 0 of 3 edges activated, XOR = F
    - All 10 triangles → F

The "0" we get is the result of the closed-loop XOR cancellation:
each triangle sees an EVEN NUMBER of the activated edges, because
the "star" pattern has the property that any cycle through it
crosses an even number of star-edges.  The cancellation is NOT
"absence of structure" — it is the witness of a closure pattern.

213 records the intermediate `δ_0 σ_v0` and the final `0` as a
`Coupling × Nat` pair.  Standard cohomology records only the `0`.
**213 has more information.**

## §4  Why 213's approach is computationally feasible

The user's last point — "모든 정보를 담아도 무한 항으로 발산을 안하니깐" —
"even storing all info doesn't diverge to infinite terms".

Standard cohomology was designed in an era when the "complex" might
be infinite-dimensional, the homology groups might have torsion,
and quotients were a way to make the algebra tractable.  For *213*,
the lattice is finite (K_5: V=5, E=10, F=10; K_5²: |C^k| ≤ 1024 in
each dimension).  No quotient is needed for tractability; full data
fits in memory.

Census on K_5² (Lean theorem `cochain_census`):

```
|C^1|        = 2^10 = 1024     (all 1-cochains explicit)
|im δ_0|     = 2^4  = 16       (coboundary representatives)
|im δ_1|     = 2^6  = 64       (cohomology classes)
|im δ_0| × |im δ_1| = 1024     (disjoint union of cosets)
```

All four quantities are stored as Bool data.  No quotient is taken;
the partition is recorded as 64 cosets, each containing 16 reps.

## §5  Connection to G6, G7

  · **G6**: "shadow / tradeoff" is empty vocabulary; finite content
    is what matters.
  · **G7**: classical existence theorems become operational ghosts
    in 213's strict ∅-axiom regime; `Classical.choice` is the
    measurable axiom delta.
  · **G8**: standard cohomology's "∂²=0 axiom" is the same kind of
    vocabulary slip — what should be a *theorem* (verifiable by
    decide on concrete cochains) is dressed up as a *postulate*
    (presupposing a structure to be axiomatized about).

In all three: 213's strict ∅-axiom standard EXPOSES the ZFC
quotient/axiom fetish as residue, not necessity.

## §6  Implication for cohomology pedagogy

When teaching cohomology to a student raised on 213-Lean:

  · DON'T present `∂²=0` as a defining axiom of chain complexes.
  · DO present `∂` first as an explicit map on explicit cochains,
    THEN observe that for any combinatorial complex, applying `∂`
    twice always returns 0 (a derived fact about how face boundaries
    cancel pairwise), and derive `∂²=0` as a *theorem* of the
    geometry.

  · DON'T present cohomology as a quotient ker/im.
  · DO present cohomology as a *partition* of the cochain space
    into cosets of im, with each coset uniquely identified by its
    syndrome (= image under the next ∂).  Both the cosets and their
    representatives are concrete data.

  · DON'T import ∞-category coherence towers.
  · DO observe that on a finite combinatorial complex, the
    "higher coherence" structure already lives in the explicit
    Bool data.

## §7  Capstone: the 21-PURE Lean witness

`Bridge/CohomologyWithoutQuotient.lean` (147 lines, 21 PURE / 0 DIRTY):

  · 6 representative `delta_sq_zero_at_*` theorems (for σ = allDown,
    allUp, v0, v01, v012, v0123).
  · Universal `delta_sq_zero_universal_K5` over all 32 spin configs.
  · 3 `trajectory_*_closes` witnesses showing the boundary trajectory
    pattern (intermediate Coupling + final 0).
  · Cohomology census theorems: |C^1| = |im δ_0| × |im δ_1| = 1024.
  · `g8_cohomology_no_quotient_capstone` bundling 12 conjuncts.

Every theorem closes by `decide`.  No axiom is invoked.  ∂²=0 is
a theorem of the geometry, not a postulate of the algebra.

---

**Status:** Mingu's observation rendered as Lean reality.  The
"axiom of ∂²=0" was always a vocabulary tic; in 213 it's just
an arithmetic identity.  213's cochain complex IS the full-data
recording the user described — no quotient, no information loss,
no forced axioms, no divergence.
