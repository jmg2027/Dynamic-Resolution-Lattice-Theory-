# Frontier — does the 213 atomic signature sit on the planarity boundary by structure?

**Status**: open observation (surfaced drawing the shapeLens step by step,
2026-06-05).  Below DRLT Validation Standard — suggestive, no derivation yet.
Artifacts: `research-notes/geometric/{shapelens_stepwise,kuratowski_213}.{py,png}`.

## The observation

Kuratowski/Wagner: a graph is planar iff it has no `K_5` or `K_{3,3}` minor.  Both
forbidden graphs are 213 structures:

- `K_n` planar ⟺ `n ≤ 4`.  `d = N_S + N_T = 5` makes `K_5` the **first** non-planar
  complete graph (`d` = planar ceiling `4` + 1).  `K_5` = the 4-simplex skeleton.
- `K_{m,n}` planar ⟺ `min(m,n) ≤ 2`.  213 has `N_T = 2`, so the canonical lattice
  `K_{3,2} = K_{N_S,N_T}` is the **last** planar complete bipartite graph; the
  `det=0` degenerate `K_{3,3}` (`Mobius213K33Bridge`) is the **first** non-planar.
  **`N_T = 2` is exactly the bipartite planarity ceiling** — an equality, not just
  "small numbers".

So the shapeLens (complete reading) leaves the plane precisely at the atomic
count, and the dimension-Lens demand (the simplex wants `d−1` dimensions) is the
same fact, made topological.

## Honest assessment

- **Strong:** `N_T = 2 = ` the `K_{m,n}` planarity bound is a precise equality.
- **Weak:** `d = 5 = ` complete-graph planar ceiling `+ 1` is suggestive but
  partly small-number coincidence (planarity thresholds and atomic counts are both
  small, so collisions are cheap).
- **Speculative link (clearly marked):** planar = genus-0-embeddable = "flattenable
  into the minimal ambient surface" = "has a 2-D exterior frame".  If 213
  atomicity (§4.3, `d=5` the unique forced atomic shape) is "the minimal count that
  cannot be flattened", then `K_5` non-planar would be a topological restatement of
  no-exterior (§5.1): the atomic structure has no lower-dimensional ambient frame.

## Deep-research confirmation (2026-06-05, `shapelens_functor.md`)

The Ringel–Youngs genus formula `γ(K_n) = ⌈(n−3)(n−4)/12⌉` makes the complete
half exact-at-the-value: `γ(K_n)` is `0` for `n ≤ 4` and jumps to `1` at exactly
`n = 5` (then `0` again only nowhere — it is monotone past 5).  For the bipartite
half, `γ(K_{m,2}) ≡ 0` for **all** `m` (every `K_{m,2}` is planar), so `N_T = 2`
is confirmed the *exact* ceiling: `K_{3,2}` planar, `K_{3,3}` (genus 1) the first
non-planar — the equality is genuine, not a small-number collision.  The grading
above stands: `N_T = 2` exact, `d = 5 =` ceiling `+1` partly coincidental.

## The open question

Is there a derivation `213-atomicity ⟹ non-embeddability in genus 0` (or
`⟺ the planarity thresholds`)?  Or is it small-number coincidence with one exact
hit (`N_T=2`)?  A test: does the next atomic tier / a different `(N_S,N_T)` track
the planarity/genus thresholds, or only `(3,2,5)`?  (E.g. genus of `K_n`, `K_{m,n}`
vs the CD-tower counts.)  Not pursued; recorded as a standing thread.
