# Promotion / Essay event log

Append-only ledger of **promotion-ㄱ** and **essay-ㄱ** triggers, so the
originator can review *when* and *why* these happen across sessions and
later decide whether the situations pattern-ize (→ a heuristic, a gate, or
an automated trigger).

This is a volatile process ledger (tier-1).  No permanent tier cites it.
It is reviewed by a human, not consumed by the build.

## How to append (for every future session)

When the originator says **"프로모션 ㄱ"** (promote) or **"에세이 ㄱ"**
(essay) — or the `process` / `essay` skill runs a promotion/essay — add one
row.  Capture the *situation*, not just the artifact: what had just
happened that made promotion/essay feel right at that moment.  Newest at
the bottom.

| # | Date | Type | Topic / target | Situation (what prompted it — the pattern-able signal) | Outcome (path) |
|---|------|------|----------------|--------------------------------------------------------|----------------|

Columns:
- **Type** — `promotion` (Lean sub-tree → `theory/` chapter) or `essay`
  (cross-cutting question → `theory/essays/`).
- **Situation** — the trigger context: a sub-tree just closed `∅`-axiom?
  an iff finally completed both directions?  a question kept recurring in
  chat?  a cross-domain pattern became visible?  This column is the point
  of the log.
- **Outcome** — the chapter/essay path written (or "deferred — reason").

## Log

| # | Date | Type | Topic / target | Situation (what prompted it) | Outcome (path) |
|---|------|------|----------------|------------------------------|----------------|
| 1 | 2026-06-04 | essay | the frontier has a form (νF) | G182 essay-in-waiting; the νF-population arc closed ∅-axiom (§18 free swap-action) on a now-reconciled branch — the "essay-in-waiting" had its anchors proven | `theory/essays/foundations/the_frontier_has_a_form.md` (G182 archived) |
| 2 | 2026-06-04 | promotion | frozen = dynamic φ (§5.7) | a closed ∅-axiom result (`PhiFrozenDynamic.frozen_eq_dynamic_phi`, 2 PURE) had **no** `theory/` narrative — gap found while pursuing the ε₀/φ adjacents | `theory/math/algebra/phi_self_similarity.md` §3.6 |
| 3 | 2026-06-04 | essay | the residue unit's odometer | a multi-section Lean sub-tree (`Theory/Raw/Odometer` 41 + `OdometerValue` 18 + `ZeckendorfCarry` 7 = 66 PURE) matured into a coherent new sub-theory (the residue-unit `+1` dynamics) — closed arc needing one narrative home | `theory/essays/foundations/the_residue_unit_odometer.md` |
| 4 | 2026-06-04 | promotion | G178 + G181 (archive) | both frontier notes fully resolved (νF population + C-phys bridges + odometer/Zeckendorf cross-arc); content promoted to the foundations essay triptych — sink check 0, so the cycle's archive step ran | `archive/G178_…`, `archive/spiral_axis/G181_…` |
| 5 | 2026-06-04 | essay | the unit `1` (the residue's `+1`) | `/essay` invoked; the session's through-line — `1` proven byte-identical across ascent/descent/glue/det (C3-phys `unit_bridges_dynamics_and_readings`) + carry/Cassini/reciprocal — wanted a cross-frame synthesis distinct from the odometer-as-map essay (this is the `+1` as shared *value*, not as map) | in-conversation (not saved; candidate `theory/essays/foundations/the_unit.md` if canonicalised) |

## Reading the log later (pattern analysis)

Once there are ~10+ rows, look for:
- **Recurring situations** → a candidate *promotion trigger* (e.g. "every
  time an iff closes both directions, promotion follows" → make iff-closure
  the trigger).
- **Essay triggers** → which kinds of questions become essays (recurring
  chat question?  cross-domain synthesis?  a corrected misconception?).
- **Lag** → how long a sub-tree stays closed-but-unpromoted; a long lag
  suggests the promotion gate or the prompt is the bottleneck.
- Feed findings into `frontiers/research_grade_closure_gate.md` and, if
  stable, into `theory/PROMOTION_CRITERIA.md` / the `process` skill.
