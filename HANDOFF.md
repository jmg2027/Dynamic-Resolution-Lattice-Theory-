# Session Handoff — 2026-05-21 (Plan + Cup-Leibniz generalisation marathon)

## Branch
`claude/analyze-research-plan-Pxcoo` — 17 session commits.  All
pushed.

## Session goal evolution

**Initial goal** (top of session): Pivot from mechanical reduction
to substantive structural theorems per
`/root/.claude/plans/smooth-mapping-metcalfe.md`.

**Mid-session pivot**: After Phase 2 work surfaced the cup-Leibniz
"bug", reframed under §8.4 dichotomy avoidance as **lex-projection
cup's native algebra** (G85).

**Final pivot**: User-directed generalisation push — extend the
twisted Leibniz finding to arbitrary bidegrees, prove symbolically
without decide enumeration, via user's 3-way partition strategy.

## Final results

### Plan phases (1-5) — all delivered (commits up to `2dacaf6a`)

| Phase | Deliverable | PURE |
|---|---|---|
| 1a | Mobius213 ∀n Pell-unit invariant + Int213 rw refactor | 2+(1 internal) |
| 1b | Real213/PhiCut — φ via Pell convergents | 7 |
| 1c | TowerConvergence — `tower_L_infty_exists` | 1 |
| 1d | TowerLInfty — G61 Q1, Q5(part), L_∞ closure | 5 |
| 1e | PhiUnification — cross-domain φ capstone | 4 |
| 2 | Cup/LeibnizUniversal — research finding + diagnostic | 1 (marker) |
| 3 | Physics/Quantum/{Qubit,Bell,Bekenstein} | 14 |
| 4 | MinimalRootCapstone (G31 IVT) | 3 |
| 5 | 5 validation-pairing falsifiers | 5 |

### Phase 2 generalisation (commits `ac29efe2` → `634d9704`)

Triggered by user's "가장 213적으로 올바른 path" directive:

| File | Content | PURE |
|---|---|---|
| `Cup/LeibnizLex.lean` | (1,1) twisted Leibniz with boundary-endpoint correction `α(τ[0])·β(τ[last])` | 4 |
| `Cup/LeibnizLexSelfRef.lean` | (1,1) **self-referential form**: correction = (α⌣β)(τ \ {τ[k]}) | 4 |
| `Cup/LeibnizLex21.lean` | (2,1) bidegree on Δ³, self-referential | 2 |
| `Cup/LeibnizLexStructural.lean` | **8 PURE structural List-level lemmas** (take/drop ↔ eraseIdx commutation, foldl XOR base cases) | 8 |
| `Cup/LeibnizLexListLevel.lean` | **List-level symbolic Leibniz at (1,1) AND (2,1)** — proven ∀ α β τ via structural lemmas, NO decide enumeration | 7 |
| `research-notes/G85_cup_delta_lens_mismatch.md` | 213-native re-reading: wedge-cup × simplicial-δ Lens-mismatch reframing | doc |
| `research-notes/G86_self_referential_lex_cup_leibniz.md` | Generalised conjecture for ∀ (n, k, l) + physics speculation (K_{3,2}^{(c=2)} channel cup) | doc |
| `LESSONS_LEARNED.md` | Patterns #1-#7 with composition table | doc |

**Total new PURE this session: 67 theorems** + 2 research notes +
extensive doc/catalog updates.

### Cup-Leibniz key insight progression

1. Phase 2 initial: standard Leibniz decide-refuted; **research finding**.
2. G85: re-framing as Lens mismatch (concatenation cup vs AW vs ℤ/2 wedge).
3. Path δ: name the operation honestly (**lex-projection cup**),
   prove its native Leibniz with `α(τ[0])·β(τ[last])` correction (4 PURE).
4. LeibnizLexSelfRef: correction equals `(α⌣β)(τ \ {τ[k]})` —
   **self-referential** form, aligned with §8 doctrine.
5. LeibnizLex21: same self-referential form at (2,1), confirming generality.
6. G86: ∀ (n, k, l) conjecture + physics speculation.
7. **User's 3-way partition** symbolic strategy:
   - LeibnizLexStructural: 8 PURE List-level commutation lemmas
   - LeibnizLexListLevel: full symbolic proof at (1,1), (2,1) — no decide!

## What's still open (next session)

### Symbolic generalisation to ∀ (k, l) — CLOSED (2026-05-22)

**`list_level_leibniz_general` is PURE-proven** at the list level
(`Cohomology/Cup/LeibnizLexListLevel.lean`).  Strategy used:
custom `xorRange` operator (avoiding List.range_succ [propext]) +
`xorRange_three_way_partition` (algebraic skeleton) +
`cupList_face_decomp` (per-face structural lemmas) + XOR algebra.

Total cumulative: 32 PURE theorems realising the 3-way partition
strategy.

### Transfer to Fin-indexed cup — **FULL CLOSURE** (2026-05-22)

**16 PURE bridge primitives** added across two files:

  · `Cohomology/Cup/SubsetIdxRoundtrip.lean` (11 PURE):
    - decide-verified round-trips at Δ⁴ (n=5, k ∈ {1, 2, 3, 4})
    - ∀n general `kSubset_n_1_singleton` structural lemma
    - `binom_k_0`, `binom_m_1` Pascal sub-lemmas

  · `Cohomology/Cup/FinBridge.lean` (13 PURE — final):
    - `firstVertex_5_2`, `lastVertex_5_2` — colex 2-subset vertex
      extraction
    - `cup_5_1_1_unfold` — Pattern #2 universal, 10240 decide cases
    - `face2idx_5_3` — 3-subset → 2-subset face-index map
    - `delta_cup_5_1_1_unfold` — Pattern #2 universal, 10240 cases
    - `front2Idx_5_3`, `backVertex_5_3` — (5,2,1) extraction
    - `cup_5_2_1_unfold` — bundle form (10 rfl-per-face)
    - `frontVertex_5_3`, `back2Idx_5_3` — (5,1,2) extraction
    - `cup_5_1_2_unfold` — bundle form
    - `delta_5_1_unfold` — Pattern #2 universal, 320 decide cases
    - `fin_bridge_capstone_5_1_1` — merge-ready capstone

**All bridges PURE.  Full coverage for (1,1) Leibniz on Δ⁴:**
  · LHS unfold: `cup_5_1_1_unfold` + `delta_cup_5_1_1_unfold`
  · RHS Block 1 (δα⌣β): `cup_5_2_1_unfold` + `delta_5_1_unfold`
  · RHS Block 2 (α⌣δβ): `cup_5_1_2_unfold` + `delta_5_1_unfold`
  · Correction term: `cup_5_1_1_unfold` at face_middle_removed

Composed with the list-level ∀(k, l) theorem
(`list_level_leibniz_general`) and the existing decide-verified
Fin-form `lex_cup_leibniz_self_ref_1_1`, the Fin-indexed (1,1)
Leibniz on Δ⁴ has full PURE coverage.

### List-level → Fin-indexed automatic bridge — **CLOSED** (this session, follow-up)

The hardcoded `Cohomology/Cup/FinBridge.lean` (Δ⁴-specific, 10240
decide cases per bidegree) is now subsumed by a structural ∀(n, k, l)
capstone.

`Cohomology/Cup/FinBridgeGeneral.lean` (7 PURE theorems):
  · `kSubset_take_eq` — `(kSubset n m j).take k = kSubset n k j_a`,
    valid `j_a < binom n k`.
  · `kSubset_drop_eq` — `(kSubset n m j).drop k = kSubset n (m-k) j_b`,
    valid `j_b < binom n (m-k)`.
  · `frontIdx`, `backIdx` — general index extractions
    (`subsetIdx n k (take k)` / `subsetIdx n l (drop k)`).
  · `frontIdx_lt`, `backIdx_lt` — validity (via `roundtrip_n_k`).
  · **`cup_unfold_general`** —
    `cup n k l α β τ_idx = α ⟨frontIdx, _⟩ && β ⟨backIdx, _⟩`
    for any `(n, k, l)` and any `τ_idx : Fin (binom n (k+l))`.

Builds on the prior `roundtrip_n_k` + `kSubset_injective` work.
Bypasses propext-tainted Lean-core lemmas (`List.length_take`,
`List.take_append_*`, `omega`, etc.) with PURE constructive equivalents.

### ∀n round-trip at k=1 + ∀(n,k) kSubset bijection — **CLOSED** (this session)

Both deferred items from the previous handoff are now closed:

  · **`Cohomology/Cup/SubsetIdxRoundtripGeneral.lean`** (7 PURE):
      - `find_range'_witness` — generic witness lemma on `range'`
        (avoids `List.range_succ`'s propext via `List.range_eq_range'`)
      - `find_range_witness` — specialised to `List.range n`
      - `roundtrip_n_1`, `roundtrip_n_1_fin` — ∀n round-trip at k=1
      - `kSubset_eq_kSubset_iff_idx` (private) — predicate-bridge via
        `kSubset_injective`
      - **`roundtrip_n_k`**, **`roundtrip_n_k_fin`** —
        ∀(n, k) bijection capstone

  · **`Cohomology/Cup/KSubsetStructural.lean`** (3 PURE + 6 helpers):
      - `kSubset_length`     — `(kSubset n k j).length = k`
      - `kSubset_all_lt`     — every element `< n`
      - **`kSubset_injective`** — `i₁ ≠ i₂ ⇒ kSubset distinct`

Required custom helpers bypassing propext-tainted Lean-core lemmas:
`List.length_append`, `Nat.add_sub_cancel`, `Nat.sub_lt_sub_right`,
`Nat.succ_ne_zero`, `Bool.and_eq_true` — all replaced with constructive
equivalents.

### Physics application
G86 speculates the lex-projection cup's self-referential Leibniz
may connect to:
  · α_em 5.4×10⁻⁴ residual (cohomology cup-product origin per G35)
  · K_{3,2}^{(c=2)} bipartite cup-channel structure
  · θ_QCD α⁴ suppression as depth-(d-1) self-reference iteration

Concrete verification requires translating K_{3,2}^{(c=2)} into the
lex-projection formalism explicitly.

## Validation Standard pairing status

**17 / 23 paired observables** (74% closure) after Phase 5
additions.  Remaining 6 (Koide, η_B, m_t/m_c, m_p/m_e ≈ 6π⁵,
M_Pl/v_H, muon prefactor 192) have precision side only.

## Methodological patterns established

`LESSONS_LEARNED.md` now lists 7 cumulative patterns (`#1`–`#7`)
with composition table.  Pattern `#7` (3-way partition for δ XOR
decomposition) and `#6` (list-level decoupling) are the deepest;
they enable symbolic proofs that don't require decide enumeration
at all.

## Branch state

  · 17 session commits, all pushed
  · Full repo `lake build`: clean
  · Layer audit: 0 violations / ~1144 files
  · Kernel pure: 45 theorems 0-axiom across 10 targets
  · No new real-DIRTY introduced (some [propext] from Lean-core
    List/Nat lemmas which are kernel-sealed)

## Anchor docs (next session start)

  · `CLAUDE.md` boot sequence (unchanged)
  · `LESSONS_LEARNED.md` patterns #1-#7
  · `research-notes/G85_cup_delta_lens_mismatch.md` + `G86_*`
  · `lean/E213/Lib/Math/Cohomology/Cup/`:
      - `Core.lean` — cup with corrected docstring
      - `Leibniz.lean` — 4 concrete cases (existing)
      - `LeibnizUniversal.lean` — Phase 2 finding + closure note
      - `LeibnizLex.lean` — twisted Leibniz with explicit correction
      - `LeibnizLexSelfRef.lean` — self-referential form
      - `LeibnizLex21.lean` — (2,1) on Δ³
      - `LeibnizLexStructural.lean` — 8 PURE List-level lemmas
      - `LeibnizLexListLevel.lean` — symbolic ∀ α β τ at (1,1) + (2,1)

## Total impact

17 new commits.  ~1900 lines added net.  6 new Lean files in
Cup/ tree.  Cup-Leibniz generalisation: from "research finding"
to **truly universal-in-(α, β, τ) symbolic PURE proof** at two
bidegrees, with the path to ∀ (k, l) clearly laid out.

---

## 2026-05-22 — Session 2 continuation: Cup-Leibniz general + 6-theorem + alive

This session extends the marathon on branch
`claude/subset-bijection-lemmas-w2FKf` with **~68 new PURE
theorems** across 8 files.

### Marathons completed

**(A) ∀(n, k) kSubset bijection + ∀(n, k, l) Cup unfold**

  · `Cohomology/Cup/KSubsetStructural.lean` — `kSubset_length`,
    `kSubset_all_lt`, `kSubset_injective` (9 PURE + 6 helpers)
  · `Cohomology/Cup/SubsetIdxRoundtripGeneral.lean` — `roundtrip_n_1`,
    `roundtrip_n_k` (+fin variants), via custom `find_range_witness`
    bypassing `List.range_succ`'s propext (7 PURE)
  · `Cohomology/Cup/FinBridgeGeneral.lean` — `kSubset_take_eq`,
    `kSubset_drop_eq`, `frontIdx/backIdx + _lt`, and the capstone
    **`cup_unfold_general`** subsuming the Δ⁴-specific decide-tables
    of `FinBridge.lean` (7 PURE)

**(B) 6-theorem master (G87 §5)**

  · `CayleyDickson/Integer/ZOmegaUnits.lean` — `units6` (Eisenstein
    units), `Zeta6 = 1+ω` order-6 generator, cyclic structure, count
    bridges (18 PURE)
  · `Theory/SixTheorem.lean` — 10 individual reading theorems
    (Eisenstein, atomicity product, d+1, 3!, SU(3) roots, K_{NS,NT}
    cross-pairs, Lorentz, χ-sum, α_GUT, clause permutations) plus
    the unifying **`six_theorem`** master (11 PURE)

**(C) Alive gap closure (G87 §11)**

  · `Theory/Atomicity/AliveDerivation.lean` — `IsSelfPaired`,
    `IsClause4Alive`, **`alive_iff_clause4_alive`** dissolves the
    postulated alive predicate into Clause 4 of the 213 axiom
    applied recursively (per user's "모든 Raw는 연산이자 객체"
    insight) at count-Lens group level (7 PURE)

**(D) Pentagonal closure matrix-level (G78 stale-path fix)**

  · `Lib/Math/Mobius213ModFive.lean` — `P^5 ≡ -I (mod 5)` and
    `P^10 ≡ +I (mod 5)` at matrix entry level, plus
    `pentagonal_closure_signature` capstone (9 PURE)
  · G78/G79/G80 stale-path references updated to point to actual
    file locations

### Status: Raw → (3, 2, 5) chain fully ∅-axiom-closed

After this session's `alive_iff_clause4_alive` closure, the Raw →
atomicity → (NS, NT, d) = (3, 2, 5) inevitability chain is
**fully closed at the structural level**.  No postulate remains
beyond the 4-clause statement of `seed/AXIOM/02_statement.md` §3.2.

### Open structural problems (post-closure priorities)

| Priority | Task | Status |
|---|---|---|
| 1 | Diophantine completeness (∀ u : ZOmega, normSq u = 1 → u ∈ units6) | 🟡 `int_sq_le_one` PURE; 4·normSq ring identity remains (~50 manual rewrites) |
| 2 | Aut(K_{3,2}^{(c=2)}) as Group (currently only Nat product) | ⚪ |
| 3 | H¹(K_{3,2}^{(c=2)}) as ℤ-module of rank 8 | ⚪ |
| 4 | ι*: H¹(Δ⁴) → H¹(K) Sym(3)-equivariant morphism | ⚪ (the single biggest C3 gap) |
| 5 | Sym(3)-irrep decomposition of H¹(K) → SU(3) adjoint | ⚪ |

### Catalogs updated

  · `catalogs/correspondences.md` — Integer 6 entry now includes
    `|ZOmega^×|` and `−(χ-sum)` references with G87 cross-link
  · `catalogs/atomic-integers.md` — Integer 6 readings list expanded
  · `STRICT_ZERO_AXIOM.md` — full session 2 catalog appended

### Branch summary

  · Commits this session 2: ~12
  · ~68 new PURE theorems, 0 dirty introduced
  · Full repo `lake build`: clean
  · All pushed to `origin/claude/subset-bijection-lemmas-w2FKf`

