# research-notes/archive/universe_chain/ — Möbius extension chain (archived)

**Archived 2026-05-22**: promoted to `theory/math/universe_chain.md`.

17 chain notes (G65–G81) + navigation index (G82) + closure-form
notes (G83–G84).  Cover: Nat213 type synthesis → Möbius P encoding →
Lucas seeds → pentagonal closure → SL(2, F_5) ≅ 2I → dual fillings
→ CRT decomposition.

Closed in:
  - `lean/E213/Lens/Number/Nat213/` (12 files)
  - `lean/E213/Lens/Number/Nat213/Tower/` (3 files)
  - `lean/E213/Lib/Math/Mobius213*` (5 files)
  - `lean/E213/Lib/Math/UniverseChain/` (15 files)

~115 ∅-axiom theorems total.

## Reading order

| # | Note | Theme |
|---|---|---|
| 1 | `G65_nat213_proper_type_synthesis.md` | Proper Nat213 type + nested-pair CD-recursion |
| 2 | `G66_lenses_to_Nat213.md` | Lens classification (Raw → Nat213) |
| 3 | `G68_finite_form_and_atom_of_lenses.md` | Fractal atom = Nat213.one |
| 4 | `G70_atomicity_in_lens_fractal.md` | Atomicity (2, 3, 5) — **key** |
| 5 | `G74_one_as_glue_213_spiral.md` | 1 = glue = NS − NT — **key** |
| 6 | `G75_det_is_axis_generator_fold.md` | det(P) = 1 = glue — **key** |
| 7 | `G77_lucas_mersenne_dual_seven.md` | Lucas seeds = (NT, NS), L_3 = 7 = M_3 — **key** |
| 8 | `G78_pentagonal_closure_dihedral_d5.md` | P^10 ≡ I mod 5 — ★ session-defining |
| 9 | `G79_algebraic_geometry_cohomology.md` | SL(2, F_5) ≅ 2I, K_{3,2} cohomology — **key** |
| 10 | `G80_c2_doubling_dual_fillings.md` | c = 2 doubling, dual fillings |
| 11 | `G81_crt_5_2_decomposition.md` | CRT (mod 5, mod 2) — **key** |
| 12 | `G82_chain_summary_g65_g81.md` | Navigation index (chain summary) |

Other notes (G67 absorbed by G68; G69, G71-G73, G76 active for
specific points; G83-G84 refactor strategy + closed-form pattern
unification) provide supporting context.

## Cross-references

  - **`theory/math/universe_chain.md`** — promoted narrative
  - `lean/E213/Lib/Math/UniverseChain/MobiusChain.lean` — chain sentinel
  - `theory/math/cayley_dickson/algebra_tower.md` — algebra-side
    appearance of φ (asymptote rate connects here)
  - `theory/physics/symmetry/c3_chain.md` — physics-side (K_{3,2}
    cohomology = gluon octet)
