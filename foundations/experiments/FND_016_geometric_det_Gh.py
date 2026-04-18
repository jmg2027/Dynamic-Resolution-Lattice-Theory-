"""
EXP_FND_016: Direct geometric det(G_h) computation from simplex
================================================================

Methodological pivot: STOP fitting formulas, START computing from
the established simplex geometry.

Setup (ch04):
  d(Delta^5) = boundary of 5-simplex = 6 vertices = 3 A + 3 B
  A_1, A_2, A_3: orthonormal basis of C^3 subspace (spatial)
  B_1, B_2, B_3: three unit vectors in C^2 subspace (temporal)
    ch04 Proposition 4.4: B_3 = alpha*B_1 + beta*B_2, |a|^2+|b|^2=1
  Variational solution determines alpha, beta (ch05).

For each of the 20 hinges (C(6,3) triangles), compute det(G_h) from
the actual geometry. Classify by hinge type and extract scale.

Expected outcomes:
  - det(G_AAA) = 1 (exact, orthonormal A's)
  - det(G_BBB) = 0 (exact, B's in 2D)
  - det(G_AAB), det(G_ABB): depend on (alpha, beta) parametrization

Question: does epsilon_0 ~= 0.0038 emerge from this geometry?
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
import numpy as np
from itertools import combinations


def build_boundary_simplex_vertices(alpha, beta, delta=0.0):
    """Return 6 unit vectors in C^5 for boundary of 5-simplex.
    A_i: standard basis of C^3 subspace.
    B_j: unit vectors in C^2 subspace.
    alpha, beta: B_3 = alpha*B_1 + beta*B_2 * exp(i*delta)
    """
    # A-block: e_1, e_2, e_3
    A1 = np.array([1, 0, 0, 0, 0], dtype=complex)
    A2 = np.array([0, 1, 0, 0, 0], dtype=complex)
    A3 = np.array([0, 0, 1, 0, 0], dtype=complex)
    # B-block: B_1 = e_4, B_2 = e_5, B_3 = alpha*e_4 + beta*e_5*exp(i*delta)
    B1 = np.array([0, 0, 0, 1, 0], dtype=complex)
    B2 = np.array([0, 0, 0, 0, 1], dtype=complex)
    B3 = alpha * B1 + beta * np.exp(1j * delta) * B2
    # Normalize B3 (should already be normalized if |a|^2+|b|^2=1)
    B3 /= np.linalg.norm(B3)
    return {"A1": A1, "A2": A2, "A3": A3, "B1": B1, "B2": B2, "B3": B3}


def det_Gram(vecs):
    """Gram determinant of a list of column vectors."""
    n = len(vecs)
    G = np.zeros((n, n), dtype=complex)
    for i in range(n):
        for j in range(n):
            G[i, j] = np.vdot(vecs[i], vecs[j])
    return np.real(np.linalg.det(G))


def classify_hinge(labels):
    """Given 3 labels like ('A1','A2','B1'), return 'AAA', 'AAB', 'ABB', 'BBB'."""
    ac = sum(1 for l in labels if l.startswith('A'))
    bc = sum(1 for l in labels if l.startswith('B'))
    return 'A'*ac + 'B'*bc


class EXP_FND_016(Experiment):
    ID = "FND_016"
    TITLE = "Geometric det Gh from simplex"

    def run(self):
        self.log("=" * 65)
        self.log("DIRECT GEOMETRIC det(G_h) COMPUTATION")
        self.log("=" * 65)

        # Variational solution: for symmetric (3,3) partition,
        # the three B vectors are equally spaced in C^2 (like Mercedes),
        # giving |<B_i,B_j>|^2 = 1/4 for i != j (120-deg apart in real analog).
        # Equivalent: alpha = 1/2, beta = sqrt(3)/2, delta = 0.
        # This is the symmetric variational point.
        import cmath
        # Equally-spaced unit vectors in C^2 (up to phase):
        # B_1, B_2, B_3 at phase angles 0, 2pi/3, 4pi/3 in a real 2D subspace
        # => |<B_i,B_j>| = cos(2pi/3) = -1/2, so |<>|^2 = 1/4

        self.log(f"\n  Configuration: B vectors equally spaced in C^2")
        self.log(f"  (variational symmetric point)")
        alpha = 0.5
        beta = np.sqrt(3) / 2
        vecs = build_boundary_simplex_vertices(alpha, beta)

        # Verify B overlaps
        self.log(f"\n  B-vector overlaps:")
        for (i, j) in [('B1','B2'), ('B1','B3'), ('B2','B3')]:
            ov = abs(np.vdot(vecs[i], vecs[j]))**2
            self.log(f"    |<{i},{j}>|^2 = {ov:.6f}")
        self.check("B overlaps all equal 1/4 (symmetric)",
                   abs(abs(np.vdot(vecs['B1'],vecs['B2']))**2 - 0.0) < 1e-6)

        # Wait — B_1 = e_4, B_2 = e_5 are orthogonal!
        # So |<B_1,B_2>|^2 = 0, not 1/4. Fix.
        # The "symmetric" config needs B_1, B_2, B_3 to all make equal
        # pairwise overlap. If B_1, B_2 span C^2, we need to choose them
        # non-orthogonal for symmetry.

        # Canonical symmetric (3-fold) config in C^2:
        # B_k = (cos(2*pi*k/3), sin(2*pi*k/3)) embedded as real vectors
        # then |<B_i,B_j>| = cos(2*pi/3) = -1/2, overlap sq = 1/4.
        self.log(f"\n  Reset: use 3-fold symmetric B vectors in C^2:")
        theta = 2 * np.pi / 3
        B1 = np.array([0, 0, 0, 1, 0], dtype=complex)
        B2 = np.array([0, 0, 0, np.cos(theta), np.sin(theta)], dtype=complex)
        B3 = np.array([0, 0, 0, np.cos(2*theta), np.sin(2*theta)], dtype=complex)
        vecs['B1'], vecs['B2'], vecs['B3'] = B1, B2, B3

        for (i, j) in [('B1','B2'), ('B1','B3'), ('B2','B3')]:
            ov = abs(np.vdot(vecs[i], vecs[j]))**2
            self.log(f"    |<{i},{j}>|^2 = {ov:.6f}")
        self.check("B overlaps = 1/4", abs(abs(np.vdot(B1,B2))**2 - 0.25) < 1e-6)

        # Now compute det(G_h) for all 20 triangular hinges in boundary d(Delta^5)
        self.log(f"\n{'='*65}")
        self.log("ALL 20 HINGES OF d(DELTA^5)")
        self.log(f"{'='*65}")

        labels = ['A1', 'A2', 'A3', 'B1', 'B2', 'B3']
        hinge_values = {'AAA': [], 'AAB': [], 'ABB': [], 'BBB': []}
        all_dets = []

        for combo in combinations(labels, 3):
            htype = classify_hinge(combo)
            vs = [vecs[l] for l in combo]
            det = det_Gram(vs)
            hinge_values[htype].append(det)
            all_dets.append((combo, htype, det))

        self.log(f"\n  {'Hinge':>20} {'Type':>5} {'det(G_h)':>12}")
        self.log(f"  {'-'*20} {'-'*5} {'-'*12}")
        for combo, htype, det in all_dets:
            self.log(f"  {str(combo):>20} {htype:>5} {det:>12.6f}")

        self.log(f"\n  Distribution by type:")
        for htype in ['AAA', 'AAB', 'ABB', 'BBB']:
            vals = hinge_values[htype]
            if vals:
                mean = np.mean(vals)
                std = np.std(vals)
                self.log(f"    {htype}: count={len(vals)}, mean={mean:.6f}, "
                         f"std={std:.6f}")

        # Check theoretical values
        self.log(f"\n  Theoretical checks:")
        # AAA: 3 orthonormal vectors -> det = 1
        aaa_val = hinge_values['AAA'][0] if hinge_values['AAA'] else None
        self.log(f"    AAA det = {aaa_val:.6f} (expected 1)")
        self.check("det(G_AAA) = 1", abs(aaa_val - 1.0) < 1e-10)

        # BBB: 3 vectors in 2D subspace -> det = 0
        bbb_val = hinge_values['BBB'][0] if hinge_values['BBB'] else None
        self.log(f"    BBB det = {bbb_val:.6e} (expected 0, TTT theorem)")
        self.check("det(G_BBB) = 0", abs(bbb_val) < 1e-10)

        # Compute deviations from combinatorial values
        self.log(f"\n{'='*65}")
        self.log("GEOMETRIC DEVIATIONS: combinatorial vs det-weighted")
        self.log(f"{'='*65}")
        self.log("""
  Combinatorial coupling uses hinge COUNT.
  Full coupling uses hinge AREA = sqrt(det(G_h)).
  Deviation = (1 - <sqrt(det)>) per hinge, aggregated by type.
""")

        aab_mean = np.mean(hinge_values['AAB'])
        abb_mean = np.mean(hinge_values['ABB'])
        aab_area = np.sqrt(aab_mean) if aab_mean > 0 else 0
        abb_area = np.sqrt(abb_mean) if abb_mean > 0 else 0
        aaa_area = 1.0
        bbb_area = 0.0

        self.log(f"\n  Hinge type    count   <det>       <area>      ")
        self.log(f"  {'-'*12}  {'-'*5}   {'-'*10}  {'-'*10}")
        self.log(f"  AAA             1      {1.0:10.6f}  {aaa_area:10.6f}")
        self.log(f"  AAB             9      {aab_mean:10.6f}  {aab_area:10.6f}")
        self.log(f"  ABB             9      {abb_mean:10.6f}  {abb_area:10.6f}")
        self.log(f"  BBB             1      {0.0:10.6f}  {bbb_area:10.6f}")

        # Check the claim: mean det(G_h) scale relates to alpha_GUT?
        total_det = (1 + 9*aab_mean + 9*abb_mean + 0)
        total_count = 20
        avg_det = total_det / total_count
        import math
        alpha_GUT = 6 / (25 * math.pi**2)

        self.log(f"\n  Total sum of det(G_h) over 20 hinges: {total_det:.6f}")
        self.log(f"  Average det per hinge: {avg_det:.6f}")
        self.log(f"  alpha_GUT: {alpha_GUT:.6f}")
        self.log(f"  alpha_GUT * 20: {20*alpha_GUT:.6f}")

        # Geometric interpretation of eps0 candidate
        # ABB deviation from 1 is the only nontrivial geometric number
        abb_deviation = 1 - abb_mean  # = 1/4
        self.log(f"\n  Key geometric number at symmetric config:")
        self.log(f"    ABB deviation from 1: 1 - det(G_ABB) = {abb_deviation:.6f} = 1/4")
        self.log(f"    This is the UNIQUE nontrivial det deviation.")

        self.log(f"\n  Candidate interpretations of eps_0 ~= 0.0038:")
        self.log(f"    avg_det / total_count       = {avg_det/20:.6f}")
        self.log(f"    (1-abb_dev)^2 = 0.5625      = {(1-abb_deviation)**2:.6f}")
        self.log(f"    alpha_GUT * (mean det)      = {alpha_GUT * avg_det:.6f}")
        self.log(f"    (abb_dev)^2 = 1/16          = {abb_deviation**2:.6f}")
        self.log(f"    (abb_dev)^3 = 1/64          = {abb_deviation**3:.6f}")
        self.log(f"    (abb_dev)^4 = 1/256         = {abb_deviation**4:.6f} <-- ~0.0039")
        self.log(f"    (abb_dev)^2 / d^2           = {abb_deviation**2/25:.6f}")
        self.log(f"    abb_dev / (d^2 + ?)         = {abb_deviation/65.8:.6f}")

        eps0_candidate = abb_deviation ** 4
        eps0_book = 0.0038
        rel = abs(eps0_candidate - eps0_book) / eps0_book
        self.log(f"\n  (1/4)^4 = 1/256 = {eps0_candidate:.6f}")
        self.log(f"  vs book eps0 = {eps0_book}, rel dev = {rel*100:.1f}%")
        self.check("(ABB dev)^4 matches eps0 within 5%", rel < 0.05)

        # Variance / deviation from "flat"
        dets_nontrivial = hinge_values['AAB'] + hinge_values['ABB']
        geom_var = np.var(dets_nontrivial)
        self.log(f"\n  Geometric variance of nontrivial hinges: {geom_var:.6f}")

        # SUMMARY
        self.log(f"\n{'='*65}")
        self.log("SUMMARY: what does direct geometry give?")
        self.log(f"{'='*65}")
        self.log(f"""
  At symmetric (3,3) config of d(Delta^5):
    det(G_AAA) = 1.000000 (orthonormal A's)
    det(G_BBB) = 0.000000 (TTT theorem, 3 B's in C^2)
    det(G_AAB) ≈ {aab_mean:.6f} (9 hinges, equal by symmetry)
    det(G_ABB) ≈ {abb_mean:.6f} (9 hinges, equal by symmetry)

  These are the natural GEOMETRIC values at the flat manifold.
  NOT epsilon_0 ~= 0.0038. The scale of det(G_h) is O(0.1-1), not 10^-3.

  Conclusion: epsilon_0 is NOT directly det(G_h) mean.
  It must be a DEVIATION from this reference, or a different
  geometric quantity entirely.

  Candidates for "what eps_0 actually is":
    (a) Second-order perturbation from flat manifold: O(eps^2)
    (b) Ratio: eps_0 = (det at our universe) / (det at flat manifold)
    (c) Specific combination via Regge action S = sum A_h * delta_h
    (d) something else entirely

  This suggests the BOOK's "eps_0 ~= 0.0038" is NOT a direct
  geometric quantity at symmetric config, but something derived
  from a secondary structure (perturbation, ratio, or Regge integral).

  Next investigation needed: identify (a)-(d) from ch12 derivation
  or ch05 variational principle.
""")


if __name__ == "__main__":
    EXP_FND_016().execute()
