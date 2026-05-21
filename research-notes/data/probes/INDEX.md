# research-notes/data/probes/

Raw experimental probe output from G52 algebra-tower investigation
(2026-05-09 marathon).  Sits alongside `data/raw_fold_slash_context.tsv`
as evidence base.

Probe = Python/Rust script that explored algebra-tower instances
(base D × layer L_n cross-sections) before the formalization landed in
`lean/E213/Lib/Math/CayleyDickson/Tower/`.

## Contents

| File | Probe topic |
|---|---|
| `G52_probe_hurwitz.txt` | Type D Hurwitz raid |
| `G52_probe_hurwitz_L8.txt` | Type D Hurwitz raid, L8 deep push |
| `G52_probe_mt.txt` | Multi-threaded scan |
| `G52_probe_output_2026_05_09.txt` | Base D × layer L_n cross-section (initial) |
| `G52_probe_output_L10.txt` | Mul-table optimized, L10 |
| `G52_probe_output_L6_3rows.txt` | Generic base × layer probe, 3-row L6 |
| `G52_probe_output_multibase.txt` | Multi-base cross-section |
| `G52_probe_output_ringlevel.txt` | Ring-level dim/units output |
| `G52_probe_output_zomega.txt` | Z[ω] base probe |
| `G52_probe_zomega_L8.txt` | Type C deep push (Z[ω] L8) |

## Status

Closed — findings absorbed into:
- `research-notes/G52_213_algebra_tower_layers.md` (narrative)
- `research-notes/G58_algebra_tower_completion.md` (final summary)
- `lean/E213/Lib/Math/CayleyDickson/Tower/` (formalization)

Retained as raw evidence (probe runs are not in git history of any
script; deleting these would erase the empirical record).
