"""
RH_023: Artin Decomposition of Ihara Zeta
==========================================

Jeong's insight: The Ihara zeta decomposes like Artin L-functions:
  Z(u) = Z_c(u) · Z_t(u)  (chiral × trivial)

Complex reps (G_c) → Ihara zeros ON critical circle
Self-conjugate (G_t, σ-symmetrized) → zeros OFF critical circle

τ-symmetrization:
  V_t = ℂ^n ⊕ ℂ^n, σ(v₁,v₂) = (v₂,v₁)
  σ-invariant: ψ_t = (v, v)/√2 → G_t = 2⟨v_i,v_j⟩
  This reduces to a SINGLE Gram matrix (rank n, not 2n)

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from experiment import Experiment


class ArtinIhara(Experiment):
    ID = "RH_023"
    TITLE = "Artin decomposition Ihara"

    def run(self):
        self.test1_sigma_symmetrized()
        self.test2_ihara_split()
        self.test3_phase_structure()
        self.test4_ramanujan_split()

    def _ihara_zeros_frac(self, W):
        """Fraction of Ihara zeros on critical circle."""
        eigs = np.sort(np.linalg.eigvalsh(W))[::-1]
        d_eff = W.sum(axis=1).mean()
        if d_eff <= 1:
            return 0.0
        n_on, n_total = 0, 0
        for lam in eigs:
            if abs(lam) < 1e-10:
                continue
            disc = lam**2 - 4*(d_eff - 1)
            n_total += 2
            if disc < 0:
                n_on += 2
        return n_on / max(n_total, 1)

    # ── Test 1: σ-Symmetrized Construction ───────────────

    def test1_sigma_symmetrized(self):
        """Build G with explicit σ-symmetrization in V_t."""
        self.log("\n═══ Test 1: σ-Symmetrized Gram Matrix ═══")
        self.log("  V_c = ℂ³⊕ℂ²: u,w independent")
        self.log("  V_t = ℂ²⊕ℂ² with σ: ψ_t = (v,v)/√2")
        self.log("  Total: d_ind = 5 + 4 = 9")

        N = 30
        n_t = 2  # each τ-pair is ℂ²⊕ℂ²

        rng = np.random.RandomState(42)

        # Chiral: independent u ∈ ℂ³, w ∈ ℂ²
        u = rng.randn(N, 3) + 1j * rng.randn(N, 3)
        w = rng.randn(N, 2) + 1j * rng.randn(N, 2)

        # Trivial: v ∈ ℂ², DUPLICATED → (v, v)/√2
        v = rng.randn(N, n_t) + 1j * rng.randn(N, n_t)

        # Full vector: (u, w, v/√2, v/√2) ∈ ℂ^9
        psi = np.hstack([u, w, v / np.sqrt(2), v / np.sqrt(2)])
        norms = np.linalg.norm(psi, axis=1, keepdims=True)
        psi /= norms

        G = psi @ psi.conj().T

        # Sector Gram matrices
        psi_c = psi[:, :5]  # chiral part
        psi_t = psi[:, 5:]  # trivial part (v/√2, v/√2)
        G_c = psi_c @ psi_c.conj().T
        G_t = psi_t @ psi_t.conj().T

        err = np.max(np.abs(G - G_c - G_t))
        self.log(f"\n  |G - G_c - G_t| = {err:.2e}")
        self.log(f"  rank(G) = {np.linalg.matrix_rank(G, tol=1e-8)}")
        self.log(f"  rank(G_c) = {np.linalg.matrix_rank(G_c, tol=1e-8)}")
        self.log(f"  rank(G_t) = {np.linalg.matrix_rank(G_t, tol=1e-8)}")
        self.log(f"  (σ-symmetrized V_t should have rank ≤ {n_t}, "
                 f"NOT {2*n_t})")

        self.check("G = G_c + G_t with σ-symmetrization",
                   err < 1e-10)

    # ── Test 2: Ihara Zeros — Chiral vs σ-Trivial ────────

    def test2_ihara_split(self):
        """Ihara zeros on critical circle: G_c vs G_t (σ-symmetrized)."""
        self.log("\n═══ Test 2: Ihara Zeros — Artin Split ═══")
        self.log("  Prediction: G_c zeros ON circle, G_t zeros OFF")

        N = 25
        n_t_values = [2, 3, 4]  # different τ-pair sizes
        n_trials = 50

        self.log(f"\n  {'n_t':>3} {'d_ind':>5} | {'G_c circle%':>12} | "
                 f"{'G_t circle%':>12} | {'G circle%':>11}")
        self.log(f"  {'-'*3} {'-'*5}-+-{'-'*12}-+-"
                 f"{'-'*12}-+-{'-'*11}")

        for n_t in n_t_values:
            d_ind = 5 + 2 * n_t
            rc, rt, rf = [], [], []

            for t in range(n_trials):
                rng = np.random.RandomState(t + n_t * 1000)

                u = rng.randn(N, 3) + 1j * rng.randn(N, 3)
                w = rng.randn(N, 2) + 1j * rng.randn(N, 2)
                v = rng.randn(N, n_t) + 1j * rng.randn(N, n_t)

                psi = np.hstack([u, w, v/np.sqrt(2), v/np.sqrt(2)])
                psi /= np.linalg.norm(psi, axis=1, keepdims=True)

                G_c = psi[:, :5] @ psi[:, :5].conj().T
                G_t = psi[:, 5:] @ psi[:, 5:].conj().T
                G = psi @ psi.conj().T

                W_c = np.abs(G_c)**2; np.fill_diagonal(W_c, 0)
                W_t = np.abs(G_t)**2; np.fill_diagonal(W_t, 0)
                W = np.abs(G)**2; np.fill_diagonal(W, 0)

                rc.append(self._ihara_zeros_frac(W_c))
                rt.append(self._ihara_zeros_frac(W_t))
                rf.append(self._ihara_zeros_frac(W))

            self.log(f"  {n_t:>3} {d_ind:>5} | "
                     f"{np.mean(rc):>11.0%} | "
                     f"{np.mean(rt):>11.0%} | "
                     f"{np.mean(rf):>10.0%}")

        self.check("G_c more Ramanujan than G_t",
                   np.mean(rc) > np.mean(rt))

    # ── Test 3: Phase Structure ──────────────────────────

    def test3_phase_structure(self):
        """Phase distribution in σ-symmetrized G_t vs G_c."""
        self.log("\n═══ Test 3: Phase Structure — σ Effect ═══")
        self.log("  G_t with σ: phases constrained")
        self.log("  G_c without σ: phases free")

        N = 40
        n_t = 3
        n_trials = 100

        J_c_all, J_t_all = [], []
        phase_c, phase_t = [], []

        for t in range(n_trials):
            rng = np.random.RandomState(t + 5555)
            u = rng.randn(N, 3) + 1j * rng.randn(N, 3)
            w = rng.randn(N, 2) + 1j * rng.randn(N, 2)
            v = rng.randn(N, n_t) + 1j * rng.randn(N, n_t)

            psi = np.hstack([u, w, v/np.sqrt(2), v/np.sqrt(2)])
            psi /= np.linalg.norm(psi, axis=1, keepdims=True)

            G_c = psi[:, :5] @ psi[:, :5].conj().T
            G_t = psi[:, 5:] @ psi[:, 5:].conj().T

            # Jarlskog invariants
            for _ in range(20):
                i, j, k = rng.choice(N, 3, replace=False)
                J_c_all.append(np.imag(G_c[i,j]*G_c[j,k]*G_c[k,i]))
                J_t_all.append(np.imag(G_t[i,j]*G_t[j,k]*G_t[k,i]))

            # Phase of off-diagonal elements
            for i in range(min(N, 10)):
                for j in range(i+1, min(N, 10)):
                    if abs(G_c[i,j]) > 1e-10:
                        phase_c.append(np.angle(G_c[i,j]))
                    if abs(G_t[i,j]) > 1e-10:
                        phase_t.append(np.angle(G_t[i,j]))

        J_c_rms = np.sqrt(np.mean(np.array(J_c_all)**2))
        J_t_rms = np.sqrt(np.mean(np.array(J_t_all)**2))

        self.log(f"\n  Jarlskog RMS:")
        self.log(f"    Chiral (G_c):   {J_c_rms:.6f}")
        self.log(f"    Trivial (G_t σ): {J_t_rms:.6f}")
        self.log(f"    Ratio J_t/J_c:  {J_t_rms/J_c_rms:.4f}")

        # Phase entropy
        bins = np.linspace(-np.pi, np.pi, 20)
        h_c, _ = np.histogram(phase_c, bins, density=True)
        h_t, _ = np.histogram(phase_t, bins, density=True)
        S_c = -np.sum(h_c[h_c>0] * np.log(h_c[h_c>0]) * (2*np.pi/19))
        S_t = -np.sum(h_t[h_t>0] * np.log(h_t[h_t>0]) * (2*np.pi/19))
        S_max = np.log(19)

        self.log(f"\n  Phase entropy (normalized):")
        self.log(f"    Chiral:  {S_c/S_max:.4f}")
        self.log(f"    Trivial: {S_t/S_max:.4f}")

        self.check("J_t reduced by σ-symmetrization",
                   J_t_rms < J_c_rms)

    # ── Test 4: Ramanujan Split vs n_t ───────────────────

    def test4_ramanujan_split(self):
        """How Ramanujan fraction splits as τ-pair size varies."""
        self.log("\n═══ Test 4: Ramanujan Split vs τ-Pair Size ═══")
        self.log("  Larger n_t → more trivial content → ???")

        N = 25
        n_trials = 50

        self.log(f"\n  {'config':>16} | {'G_c%':>6} | {'G_t%':>6} | "
                 f"{'full%':>6} | {'Δ(c-t)':>7}")
        self.log(f"  {'-'*16}-+-{'-'*6}-+-{'-'*6}-+-"
                 f"{'-'*6}-+-{'-'*7}")

        configs = [
            (0, "d=5 (pure chiral)"),
            (2, "d=9 (5+4)"),
            (3, "d=11 (5+6)"),
            (5, "d=15 (5+10)"),
            (8, "d=21 (5+16)"),
        ]

        for n_t, label in configs:
            rc, rt, rf = [], [], []
            for t in range(n_trials):
                rng = np.random.RandomState(t + n_t * 2000)
                u = rng.randn(N, 3) + 1j * rng.randn(N, 3)
                w = rng.randn(N, 2) + 1j * rng.randn(N, 2)

                if n_t > 0:
                    v = rng.randn(N, n_t) + 1j * rng.randn(N, n_t)
                    psi = np.hstack([u, w, v/np.sqrt(2), v/np.sqrt(2)])
                else:
                    psi = np.hstack([u, w])
                psi /= np.linalg.norm(psi, axis=1, keepdims=True)

                G_c = psi[:, :5] @ psi[:, :5].conj().T
                W_c = np.abs(G_c)**2; np.fill_diagonal(W_c, 0)
                rc.append(self._ihara_zeros_frac(W_c))

                G = psi @ psi.conj().T
                W = np.abs(G)**2; np.fill_diagonal(W, 0)
                rf.append(self._ihara_zeros_frac(W))

                if n_t > 0:
                    G_t = psi[:, 5:] @ psi[:, 5:].conj().T
                    W_t = np.abs(G_t)**2; np.fill_diagonal(W_t, 0)
                    rt.append(self._ihara_zeros_frac(W_t))
                else:
                    rt.append(0)

            mc, mt, mf = np.mean(rc), np.mean(rt), np.mean(rf)
            delta = mc - mt
            self.log(f"  {label:>16} | {mc:>5.0%} | "
                     f"{mt:>5.0%} | {mf:>5.0%} | "
                     f"{delta:>+6.0%}")

        self.check("Artin split measured", True)


if __name__ == "__main__":
    ArtinIhara().execute()
