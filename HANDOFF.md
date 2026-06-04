# Session Handoff — 2026-06-03 (∅-axiom determinant via antisymmetrization)

## Branch
`claude/goal-g183-CxU4X` — `origin/main` (invert-universal-property + concurrent threads) merged
in.  Full `cd lean && lake build` clean; every new theorem ∅-axiom (`tools/scan_axioms.py` →
`N pure / 0 dirty`, run from repo root).

## Headline this session: a complete ∅-axiom determinant

Built the Leibniz determinant and **all its defining properties** via antisymmetrization — the
natural home the determinant essay predicted (`theory/essays/determinant_as_quotient_characteristic.md`).
No `funext`/`propext`/`Quot.sound`/`Classical`/Mathlib.

- **`Linalg213/Permutation` (33 PURE)** — `LPerm`, `psign` (inversion sign), `swapAt`, the
  Leibniz determinant `leibDet n M = Σ_σ sign(σ)·Πᵢ M i (σ i)`, the per-term row-swap identity.
- **`Linalg213/PermClosure` (76 PURE)** — the symmetric-group machinery, ∅-axiom from scratch
  (core's `List.mem_*`/`length_append`/`map_map`/`range`/`Nodup` are propext/Quot-tainted):
  - clean `List` substrate (`mem_*`, `length_append'`, `map_map'`, `Nodup := ∀a, cnt a L ≤ 1`).
  - soundness + completeness (`q ∈ permsOf xs ⟺ LPerm q xs`), `nodup_permsOf` (via a `removeFirst`
    retraction), the count engine `lperm_of_cnt_eq`, and ★ `perms_swap_closed` (enumeration closed
    under `swapAt`, via a clean self-defined `iota`).
  - ★ **alternating**: `leibDet_rowSwap` (adjacent row swap negates), `leibDet_eq_zero_of_rows_eq`
    / `leibDet_eq_zero_of_two_rows_eq` / `leibDet_rows_eq_ne` (equal rows ⟹ 0, any positions).
  - ★ **multilinearity**: `leibDet_setRow_add` / `leibDet_setRow_smul` (linear in each row).
  - ★ **degeneracy**: `leibDet_proportional_rows`, `leibDet_zero_row`.
- **`Linalg213/FibCassiniDet` (3 PURE)** — `det 2 (Fibonacci Casoratian) = (−1)ⁿ⁺¹` (the unit end).
- **`Linalg213/Laplace` (4 PURE, started)** — the minor relabeling `unshift` = inverse of
  `colShift` (cofactor-expansion foundation).

## Open path (in progress) — `research-notes/G185_hadamard_linalg_program.md`

**Laplace → CH → cfiniteZ_mul** (chosen; toward the general C-finite Hadamard product):
§1 relabeling ✅ → §2 row-0 cofactor expansion `leibDet (n+1) M = Σⱼ altSign j · M 0 j ·
leibDet n (minor M j)` (the heaviest: `perms (n+1)` ↔ `⋃ⱼ perms n` reindex; sign via
`psign_cons`, product via `colShift_unshift`) → §3 any-row expansion → §4 adjugate
(`M·adj = det·I`; off-diagonal = `leibDet_rows_eq_ne` ✅) → §5 integer Cayley–Hamilton →
§6 Kronecker `M` → `cfiniteZ_mul`.

## Other live threads (earlier this branch)
- C-finite orbit dimension promoted to `theory/math/analysis/cfinite_orbit_dimension.md`
  (`Cauchy/OrbitDimension`, `Cauchy/CFiniteRing`).
- Number-tower founding (`Lens/Number/`, `book/`) merged from main.

## DRLT Validation Standard
Still the repo's stated real target (untouched): ppb-ppm precision theorem and/or a strict
∅-axiom falsifier (`N_gen=3`, `θ_QCD`).
