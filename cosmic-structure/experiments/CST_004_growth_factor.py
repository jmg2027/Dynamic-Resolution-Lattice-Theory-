"""
CST_004: Structure Growth Factor f(z)*sigma_8 from DRLT
=========================================================
Joint research by Mingu Jeong and Claude (Anthropic).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from drlt import D, N_S, N_T, ALPHA_GUT, dark_energy_fraction
from experiment import Experiment

_trapz = getattr(np, 'trapezoid', getattr(np, 'trapz', None))


class GrowthFactor(Experiment):
    ID = "CST_004"
    TITLE = "Structure Growth Factor"

    def run(self):
        OL = dark_energy_fraction()
        Om = 1.0 - OL
        h = 0.674
        sig8 = 0.7935  # from CST_002

        self.log("\n=== DRLT Parameters ===\n")
        self.log(f"  Om = {Om:.5f},  OL = {OL:.5f}")
        self.log(f"  w  = -1 (exact)")
        self.log(f"  sigma_8 = {sig8}")

        # === Growth index gamma ===
        # For w=-1 LCDM: gamma = 6/11 (exact in GR)
        gamma_GR = 6.0/11  # 0.5455
        self.log(f"\n=== Growth Index gamma ===\n")
        self.log(f"  DRLT: w=-1 exactly => gamma = 6/11 = {gamma_GR:.4f}")
        self.log(f"  Modified gravity (DGP): gamma = 11/16 = 0.6875")
        self.log(f"  DRLT prediction is TESTABLE: gamma != 6/11")
        self.log(f"  would falsify DRLT (requires w != -1).")

        # === f*sigma_8 at various redshifts ===
        self.log(f"\n=== f(z)*sigma_8(z) Predictions ===\n")

        # Growth factor D(a) via ODE integration
        # D'' + (3-3wOL/2)(D'/a) - (3/2)Om D/a^2 = 0
        # For w=-1: H^2(a) = H0^2 [Om/a^3 + OL]
        a_arr = np.linspace(0.001, 1.0, 10000)
        da = a_arr[1] - a_arr[0]

        # Integrate growth equation using Euler method
        # D'(a) = dD/da, D''(a) = d^2D/da^2
        # Using variable x = lna: dD/dx = a dD/da
        # Better: direct numerical integration of D(a)
        # D(a) = (5Om/2) H(a) int_0^a da'/(a'H(a'))^3

        def H_over_H0(a):
            return np.sqrt(Om/a**3 + OL)

        # Growth factor via integral
        def growth_D(a_eval):
            aa = np.linspace(1e-6, a_eval, 5000)
            integrand = 1.0 / (aa * H_over_H0(aa))**3
            return (5*Om/2) * H_over_H0(a_eval) * _trapz(integrand, aa)

        # Compute D(a) and normalize to D(1)
        D_arr = np.array([growth_D(a) for a in a_arr])
        D0 = D_arr[-1]
        D_norm = D_arr / D0  # D(z=0) = 1

        # f = dlnD/dlna = (a/D)(dD/da)
        dDda = np.gradient(D_arr, a_arr)
        f_arr = a_arr * dDda / D_arr

        # sigma_8(z) = sigma_8(0) * D(z)/D(0) = sig8 * D_norm
        sig8_z = sig8 * D_norm

        # f*sig8
        fsig8 = f_arr * sig8_z

        # Observational data (RSD measurements)
        # z, f*sig8, error
        obs = [
            (0.02, 0.428, 0.048),   # 6dF
            (0.15, 0.490, 0.145),   # SDSS MGS
            (0.38, 0.497, 0.045),   # BOSS lowz
            (0.51, 0.459, 0.038),   # BOSS CMASS
            (0.61, 0.436, 0.034),   # BOSS highz
            (0.70, 0.473, 0.041),   # eBOSS
            (0.85, 0.315, 0.095),   # DESI
            (1.48, 0.462, 0.045),   # eBOSS QSO
        ]

        self.log(f"  {'z':<6} {'f*sig8':>8} {'obs':>8}"
                 f" {'err':>6} {'sigma':>8}")
        self.log(f"  {'-'*38}")

        n_good = 0
        for z, fs8_obs, err in obs:
            a = 1.0/(1+z)
            idx = np.argmin(np.abs(a_arr - a))
            fs8_pred = fsig8[idx]
            sigma = (fs8_pred - fs8_obs) / err
            self.log(f"  {z:<6.2f} {fs8_pred:>8.3f} {fs8_obs:>8.3f}"
                     f" {err:>6.3f} {sigma:>+8.2f}")
            if abs(sigma) < 2:
                n_good += 1

        self.check(f"f*sig8: {n_good}/{len(obs)} within 2sig",
                    n_good >= len(obs) - 1)

        # === Growth rate f(z) = Om(z)^gamma ===
        self.log(f"\n=== Approximation Check ===\n")
        self.log(f"  f(z) ~ Om(z)^gamma,  gamma = 6/11")

        for z in [0, 0.3, 0.5, 1.0, 2.0]:
            a = 1/(1+z)
            Om_z = Om/a**3 / H_over_H0(a)**2
            f_approx = Om_z**gamma_GR
            idx = np.argmin(np.abs(a_arr - a))
            f_exact = f_arr[idx]
            self.log(f"  z={z:.1f}: Om(z)={Om_z:.4f}"
                     f"  f_approx={f_approx:.4f}"
                     f"  f_exact={f_exact:.4f}"
                     f"  diff={abs(f_approx-f_exact):.4f}")

        self.check("gamma=6/11 approx <1% at z=0",
                    abs(Om**gamma_GR - f_arr[-1]) < 0.01)

        # === f*sig8 at z=0 ===
        fs8_0 = f_arr[-1] * sig8
        self.log(f"\n=== z=0 Prediction ===")
        self.log(f"  f(0)     = {f_arr[-1]:.4f}")
        self.log(f"  f*sig8(0)= {fs8_0:.4f}")
        self.log(f"  Observed = 0.428 +/- 0.048 (6dF)")

        self.log(f"\n=== Summary ===")
        self.log(f"  gamma = 6/11 = 0.5455 (DRLT: w=-1 exact)")
        self.log(f"  f*sig8(0) = {fs8_0:.4f}")


if __name__ == "__main__":
    GrowthFactor().execute()
