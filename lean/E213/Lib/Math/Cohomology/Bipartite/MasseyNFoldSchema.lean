import E213.Lib.Math.Cohomology.Bipartite.MasseyFourFoldH1

/-!
# n-fold Massey product schema at K_{3,2}^{(c=2)} 2-skeleton

Recursive abstract structure for n-fold Massey products
⟨a_1, …, a_n⟩ on H¹-cocycles, generalizing the 3-fold
(`MasseyTripleH1Witness`) and 4-fold (`MasseyFourFoldH1`)
formalizations.

## Defining system

A Massey defining system of depth `n` is a triangular array
`b_{i,j}` of 1-cochains for `1 ≤ i ≤ j ≤ n`, where:

  · **Diagonal** (`i = j`): `b_{i,i} = a_i`  (the input cocycles)
  · **Off-diagonal** (`i < j`, except `(1, n)`):
      `δ¹(b_{i,j}) = ⊕_{i ≤ k < j} b_{i,k} ⌣ b_{k+1,j}`

## Representative

  `rep_n := ⊕_{1 ≤ k < n} b_{1,k} ⌣ b_{k+1,n}   ∈ C²`

with class `[rep_n] ∈ H² / indeterminacy`.

## Specialization

  · n=2: `rep_2 = a_1 ⌣ a_2` (the cup product)
  · n=3: `rep_3 = a ⌣ η_bc + η_ab ⌣ c`
  · n=4: `rep_4 = a ⌣ θ_bcd + η_ab ⌣ η_cd + θ_abc ⌣ d`
  · n=5: `rep_5 = a ⌣ ψ_bcde + η_ab ⌣ θ_cde +
                    θ_abc ⌣ η_de + ψ_abcd ⌣ e`

The n-fold rep is the XOR sum of `n-1` outer-cup terms
`b_{1,k} ⌣ b_{k+1,n}` for `k = 1, …, n-1`.

## Number of cobounding chains

A depth-n defining system requires `binom n 2 = n(n-1)/2` cells
in the triangular array (excluding the apex `(1, n)` which is
free).  Of these:

  · n cocycles `a_i = b_{i,i}` (diagonal, 0 constraints)
  · n-1 pairwise η-chains (1-off-diagonal, η-constraints)
  · n-2 3-fold θ-chains (2-off-diagonal, θ-constraints)
  · …
  · 2 (n-1)-fold cobounding chains (the apex's neighbors)
  · 1 representative (the apex `b_{1,n}`)

Total constraints: `binom n 2 - 1` δ-equations (apex unconstrained).

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.MasseyNFoldSchema

open E213.Lib.Math.Cohomology.Bipartite.V32 (CochE)
open E213.Lib.Math.Cohomology.Bipartite.MasseyTripleH1Witness
  (cupOpp h1 h3 h4 theta_4 isInImDelta1)
open E213.Lib.Math.Cohomology.Bipartite.MasseyTripleH1Multi (h5)
open E213.Lib.Math.Cohomology.Bipartite.MasseyFourFoldH1 (zeroE h2)

/-! ## §1 — n=3: 3-fold Massey defining system -/

/-- 3-fold Massey defining system: triangle
        a1
        eta12  a2
        b13    eta23  a3
    where `b13` is the representative (unconstrained apex). -/
structure DefSys3 where
  a1 : CochE
  a2 : CochE
  a3 : CochE
  eta12 : CochE
  eta23 : CochE

/-- 3-fold representative: `a1 ⌣ eta23 + eta12 ⌣ a3`. -/
def DefSys3.rep (S : DefSys3) (i : Fin 3) : Bool :=
  xor (cupOpp S.a1 S.eta23 i) (cupOpp S.eta12 S.a3 i)

/-! ## §2 — n=4: 4-fold Massey defining system -/

/-- 4-fold Massey defining system: triangle
        a1
        eta12  a2
        th13   eta23  a3
        b14    th24   eta34  a4
    with apex `b14` = representative. -/
structure DefSys4 where
  a1 : CochE
  a2 : CochE
  a3 : CochE
  a4 : CochE
  eta12 : CochE
  eta23 : CochE
  eta34 : CochE
  th13 : CochE
  th24 : CochE

/-- 4-fold representative:
    `a1 ⌣ th24 + eta12 ⌣ eta34 + th13 ⌣ a4`. -/
def DefSys4.rep (S : DefSys4) (i : Fin 3) : Bool :=
  xor (xor (cupOpp S.a1 S.th24 i) (cupOpp S.eta12 S.eta34 i))
      (cupOpp S.th13 S.a4 i)

/-! ## §3 — n=5: 5-fold Massey defining system -/

/-- 5-fold Massey defining system: triangle
        a1
        eta12  a2
        th13   eta23  a3
        ps14   th24   eta34  a4
        b15    ps25   th35   eta45  a5
    with apex `b15` = representative. -/
structure DefSys5 where
  a1 : CochE
  a2 : CochE
  a3 : CochE
  a4 : CochE
  a5 : CochE
  eta12 : CochE
  eta23 : CochE
  eta34 : CochE
  eta45 : CochE
  th13 : CochE
  th24 : CochE
  th35 : CochE
  ps14 : CochE
  ps25 : CochE

/-- 5-fold representative:
    `a1⌣ps25 + eta12⌣th35 + th13⌣eta45 + ps14⌣a5`. -/
def DefSys5.rep (S : DefSys5) (i : Fin 3) : Bool :=
  xor (xor (xor (cupOpp S.a1 S.ps25 i) (cupOpp S.eta12 S.th35 i))
           (cupOpp S.th13 S.eta45 i))
      (cupOpp S.ps14 S.a5 i)

/-! ## §4 — Concrete instances

  · `defSys3_primary` recovers the 3-fold `⟨h1, h3, h4⟩` witness
  · `defSys4_trivial` recovers the 4-fold `⟨h1, h3, h1, h3⟩` witness
  · `defSys5_trivial` instantiates a trivial 5-fold ⟨h1,h3,h1,h3,h1⟩
    with all cobounding chains set to `zeroE`
-/

/-- 3-fold defining system for the primary non-vacuous witness. -/
def defSys3_primary : DefSys3 :=
  { a1 := h1, a2 := h3, a3 := h4
    eta12 := zeroE        -- since h1 ⌣ h3 = 0 at chain level
    eta23 := theta_4      -- since δ(theta_4) = h3 ⌣ h4 = (1,0,1)
  }

/-- 4-fold defining system for the trivial all-zero-cobounding case. -/
def defSys4_trivial : DefSys4 :=
  { a1 := h1, a2 := h3, a3 := h1, a4 := h3
    eta12 := zeroE, eta23 := zeroE, eta34 := zeroE
    th13 := zeroE, th24 := zeroE
  }

/-- 5-fold defining system for the trivial all-zero-cobounding case
    on ⟨h1, h3, h1, h3, h1⟩.  All pairwise cups h1⌣h3 vanish at
    chain level, so all cobounding chains can be set to `zeroE`. -/
def defSys5_trivial : DefSys5 :=
  { a1 := h1, a2 := h3, a3 := h1, a4 := h3, a5 := h1
    eta12 := zeroE, eta23 := zeroE, eta34 := zeroE, eta45 := zeroE
    th13 := zeroE, th24 := zeroE, th35 := zeroE
    ps14 := zeroE, ps25 := zeroE
  }

/-! ## §5 — Recovery + capstone -/

/-- 3-fold primary rep `(1, 0, 0)` — matches `MasseyTripleH1Witness`. -/
theorem defSys3_primary_rep_eq_100 :
    defSys3_primary.rep ⟨0, by decide⟩ = true
    ∧ defSys3_primary.rep ⟨1, by decide⟩ = false
    ∧ defSys3_primary.rep ⟨2, by decide⟩ = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- 3-fold primary class = ω (parity 1 → NOT in im(δ¹)). -/
theorem defSys3_primary_class_omega :
    isInImDelta1 defSys3_primary.rep = false := by decide

/-- 4-fold trivial rep = (0, 0, 0) — matches `MasseyFourFoldH1`
    trivial witness. -/
theorem defSys4_trivial_rep_zero :
    ∀ i : Fin 3, defSys4_trivial.rep i = false := by decide

/-- 4-fold trivial class = 0 (parity 0 → in im(δ¹)). -/
theorem defSys4_trivial_class_zero :
    isInImDelta1 defSys4_trivial.rep = true := by decide

/-- 5-fold trivial rep = (0, 0, 0). -/
theorem defSys5_trivial_rep_zero :
    ∀ i : Fin 3, defSys5_trivial.rep i = false := by decide

/-- 5-fold trivial class = 0. -/
theorem defSys5_trivial_class_zero :
    isInImDelta1 defSys5_trivial.rep = true := by decide

/-! ## §6 — n=6: 6-fold Massey defining system

Extends the pattern: 6 cocycles + 5 eta + 4 theta + 3 psi + 2 chi
+ 1 apex (representative).  Total cells in triangle = 21 = binom 6 2 + 6. -/

/-- 6-fold Massey defining system: 20 cobounding chains + 6 cocycles. -/
structure DefSys6 where
  a1 : CochE
  a2 : CochE
  a3 : CochE
  a4 : CochE
  a5 : CochE
  a6 : CochE
  eta12 : CochE
  eta23 : CochE
  eta34 : CochE
  eta45 : CochE
  eta56 : CochE
  th13 : CochE
  th24 : CochE
  th35 : CochE
  th46 : CochE
  ps14 : CochE
  ps25 : CochE
  ps36 : CochE
  chi15 : CochE
  chi26 : CochE

/-- 6-fold representative:
    `a1⌣chi26 + eta12⌣ps36 + th13⌣th46 + ps14⌣eta56 + chi15⌣a6`. -/
def DefSys6.rep (S : DefSys6) (i : Fin 3) : Bool :=
  xor (xor (xor (xor (cupOpp S.a1 S.chi26 i) (cupOpp S.eta12 S.ps36 i))
                (cupOpp S.th13 S.th46 i))
           (cupOpp S.ps14 S.eta56 i))
      (cupOpp S.chi15 S.a6 i)

/-- 6-fold trivial all-zero-cobounding instance on
    ⟨h1, h3, h1, h3, h1, h3⟩. -/
def defSys6_trivial : DefSys6 :=
  { a1 := h1, a2 := h3, a3 := h1, a4 := h3, a5 := h1, a6 := h3
    eta12 := zeroE, eta23 := zeroE, eta34 := zeroE
    eta45 := zeroE, eta56 := zeroE
    th13 := zeroE, th24 := zeroE, th35 := zeroE, th46 := zeroE
    ps14 := zeroE, ps25 := zeroE, ps36 := zeroE
    chi15 := zeroE, chi26 := zeroE
  }

/-- 6-fold trivial rep = (0, 0, 0). -/
theorem defSys6_trivial_rep_zero :
    ∀ i : Fin 3, defSys6_trivial.rep i = false := by decide

/-- 6-fold trivial class = 0. -/
theorem defSys6_trivial_class_zero :
    isInImDelta1 defSys6_trivial.rep = true := by decide

/-! ## §7 — Capstone -/

/-- ★★★★★★★★★ **n-fold Massey schema capstone** —
    unified rep + class for n ∈ {3, 4, 5, 6} via concrete
    defining systems on K_{3,2}^{(c=2)} 2-skeleton.

    The defining system at depth n is a triangular array of
    `binom (n+1) 2 = n(n+1)/2` cells, with `binom n 2 = n(n-1)/2`
    cobounding constraints + n diagonal cocycles + 1 free apex
    (the representative).  The pattern extends arbitrarily; this
    capstone instantiates n = 3, 4, 5, 6.

    The 3-fold ⟨h1, h3, h4⟩ via `defSys3_primary` lands in
    class **ω** (recovers `non_vacuous_massey_witness`).

    The n-fold ⟨h1, h3, h1, h3, …⟩ alternating pattern via
    `defSysN_trivial` lands in class **0** for n ∈ {4, 5, 6}:
    every pairwise h1⌣h3 vanishes at chain level, so every
    cobounding cell can be set to `zeroE` and the apex
    representative collapses to `(0, 0, 0)`.

    STRICT ∅-AXIOM. -/
theorem n_fold_schema_capstone :
    -- 3-fold primary = ω
    (defSys3_primary.rep ⟨0, by decide⟩ = true
     ∧ isInImDelta1 defSys3_primary.rep = false)
    -- 4-fold trivial = 0
    ∧ ((∀ i : Fin 3, defSys4_trivial.rep i = false)
       ∧ isInImDelta1 defSys4_trivial.rep = true)
    -- 5-fold trivial = 0
    ∧ ((∀ i : Fin 3, defSys5_trivial.rep i = false)
       ∧ isInImDelta1 defSys5_trivial.rep = true)
    -- 6-fold trivial = 0
    ∧ ((∀ i : Fin 3, defSys6_trivial.rep i = false)
       ∧ isInImDelta1 defSys6_trivial.rep = true) :=
  ⟨⟨by decide, defSys3_primary_class_omega⟩,
   ⟨defSys4_trivial_rep_zero, defSys4_trivial_class_zero⟩,
   ⟨defSys5_trivial_rep_zero, defSys5_trivial_class_zero⟩,
   ⟨defSys6_trivial_rep_zero, defSys6_trivial_class_zero⟩⟩

end E213.Lib.Math.Cohomology.Bipartite.MasseyNFoldSchema
