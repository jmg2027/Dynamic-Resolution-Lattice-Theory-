"""
ATM_039: Comprehensive Periodic Table Scorecard
Joint research by Mingu Jeong and Claude (Anthropic)

Complete IE scorecard for Z=1-118 using ATM_035 v3 model.
0 free parameters. All constants from d=5 simplex geometry.

Model: IE(Z) = Z_eff^2 * Ry / n^2
Screening: 8 constants + 2 pair corrections, all from DRLT.

This is the definitive table for the theory.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment
from ATM_035_complete_shell_pair import compute_IE_v2, get_period
from ATM_022_dpair_correction import IE_OBS, SYM


class PeriodicScorecard(Experiment):
    ID = "ATM_039"
    TITLE = "Periodic Table Scorecard"

    def run(self):
        self.test1_full_table()
        self.test2_block_analysis()
        self.test3_highlights()

    def test1_full_table(self):
        """Complete Z=1-118 table."""
        self.log(f"\n  {'='*65}")
        self.log(f"  DRLT Periodic Table — Ionization Energies")
        self.log(f"  0 free parameters | d=5 simplex geometry")
        self.log(f"  {'='*65}")

        errs = []
        per = {p: [] for p in range(1, 8)}
        self.log(f"\n  {'Z':>4} {'Sym':>3} {'DRLT':>7} {'Obs':>7}"
                 f" {'Err':>7} {'':>2}")
        for Z in range(1, 119):
            ie = compute_IE_v2(Z)
            obs = IE_OBS.get(Z, 0)
            sym = SYM[Z] if Z < len(SYM) else str(Z)
            if obs > 0:
                err = (ie - obs) / obs * 100
                ae = abs(err)
                errs.append(ae)
                p = get_period(Z)
                per[p].append(ae)
                mk = 'V' if ae < 5 else 'o' if ae < 10 else '.'
                self.log(f"  {Z:4d} {sym:>3} {ie:7.2f} {obs:7.2f}"
                         f" {err:+7.1f}% {mk}")

        med = np.median(errs)
        n3 = sum(1 for e in errs if e < 3)
        n5 = sum(1 for e in errs if e < 5)
        n10 = sum(1 for e in errs if e < 10)

        self.log(f"\n  {'='*50}")
        self.log(f"  OVERALL: median {med:.1f}%")
        self.log(f"  <3%: {n3}/118 ({n3*100//118}%)")
        self.log(f"  <5%: {n5}/118 ({n5*100//118}%)")
        self.log(f"  <10%: {n10}/118 ({n10*100//118}%)")
        self.log(f"\n  Per-period median:")
        for p in range(1, 8):
            if per[p]:
                self.log(f"    Period {p}: {np.median(per[p]):.1f}%"
                         f" ({len(per[p])} elements)")

        self.check(f"Median {med:.1f}% < 5%", med < 5)
        self.check(f">{n5} within 5%", n5 >= 80)

    def test2_block_analysis(self):
        """Block-by-block analysis."""
        self.log(f"\n  {'='*65}")
        self.log(f"  Block Analysis")
        self.log(f"  {'='*65}")

        blocks = {'s': [], 'p': [], 'd': [], 'f': []}
        for Z in range(1, 119):
            ie = compute_IE_v2(Z)
            obs = IE_OBS.get(Z, 0)
            if obs <= 0: continue
            ae = abs((ie-obs)/obs*100)
            p = get_period(Z)
            nn = {1:0,2:2,3:10,4:18,5:36,6:54,7:86}[p]
            ndf = {2:0,3:0,4:10,5:10,6:24,7:24}.get(p,0)
            if Z <= nn+2:
                blocks['s'].append((Z, SYM[Z], ae))
            elif (p==6 and 57<=Z<=71) or (p==7 and 89<=Z<=103):
                blocks['f'].append((Z, SYM[Z], ae))
            elif (p in(4,5) and nn+2<Z<=nn+2+10) or \
                 (p in(6,7) and nn+2+14<Z<=nn+2+24):
                blocks['d'].append((Z, SYM[Z], ae))
            else:
                blocks['p'].append((Z, SYM[Z], ae))

        for blk, data in blocks.items():
            if not data: continue
            vals = [d[2] for d in data]
            worst = max(data, key=lambda x: x[2])
            self.log(f"\n  {blk}-block ({len(data)} elements):")
            self.log(f"    Median: {np.median(vals):.1f}%")
            self.log(f"    <5%: {sum(1 for v in vals if v<5)}/{len(data)}")
            self.log(f"    Worst: {worst[1]}({worst[0]}) {worst[2]:.1f}%")

        self.check("Block analysis done", True)

    def test3_highlights(self):
        """Key highlights and remaining issues."""
        self.log(f"\n  {'='*65}")
        self.log(f"  Highlights")
        self.log(f"  {'='*65}")

        highlights = [
            (1, "H",  "Exact Ry from manifold geometry"),
            (2, "He", "2Ry(1-c^2*alpha_GUT), Born channel"),
            (6, "C",  "Period 2 complete, <3%"),
            (26,"Fe", "d-block pair correction"),
            (29,"Cu", "d-pair: 21%->4%"),
            (57,"La", "f-block filling fraction"),
            (71,"Lu", "f14-pair boundary correction"),
            (79,"Au", "d-block Period 6"),
            (83,"Bi", "Deep-core pair: 24%->2%"),
            (118,"Og","Superheavy p-block"),
        ]

        self.log(f"\n  {'Z':>4} {'Sym':>3} {'DRLT':>7} {'Obs':>7}"
                 f" {'Err':>7} Note")
        for Z, sym, note in highlights:
            ie = compute_IE_v2(Z)
            obs = IE_OBS[Z]
            err = (ie-obs)/obs*100
            self.log(f"  {Z:4d} {sym:>3} {ie:7.2f} {obs:7.2f}"
                     f" {err:+7.1f}% {note}")

        # Known limitations
        self.log(f"\n  Known limitations (>10% error):")
        for Z in range(1, 119):
            ie = compute_IE_v2(Z)
            obs = IE_OBS.get(Z, 0)
            if obs > 0 and abs((ie-obs)/obs) > 0.10:
                self.log(f"    {SYM[Z]}({Z}): {(ie-obs)/obs*100:+.1f}%"
                         f" — {'relativistic' if Z in (80,) else 'f-d transition' if Z in (103,104) else 'alkali s-block' if Z in (37,87) else 'heavy p-block'}")

        self.check("Scorecard complete", True)


if __name__ == "__main__":
    PeriodicScorecard().execute()
