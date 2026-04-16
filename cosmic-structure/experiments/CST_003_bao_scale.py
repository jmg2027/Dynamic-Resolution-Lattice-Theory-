"""
CST_003: BAO Scale & Sound Horizon from DRLT
==============================================
Joint research by Mingu Jeong and Claude (Anthropic).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from math import comb
from drlt import D, N_S, N_T, ALPHA_GUT, dark_energy_fraction
from experiment import Experiment

_trapz = getattr(np, 'trapezoid', getattr(np, 'trapz', None))


class BAOScale(Experiment):
    ID = "CST_003"
    TITLE = "BAO Scale and Sound Horizon"

    def run(self):
        OL = dark_energy_fraction()
        Om = 1.0 - OL
        DM_b = D + 1.0/N_S
        Ob = Om / (1.0 + DM_b)
        h = 0.674
        om_h2, ob_h2 = Om*h**2, Ob*h**2
        T_cmb = 2.7255  # K

        self.log("\n=== DRLT Parameters ===\n")
        self.log(f"  Om={Om:.5f}  Ob={Ob:.5f}  h={h}")
        self.log(f"  om_h2={om_h2:.5f}  ob_h2={ob_h2:.5f}")

        # === Sound horizon computation ===
        self.log(f"\n=== Sound Horizon r_d ===\n")

        # Radiation density
        T4 = (T_cmb/2.7)**4
        om_r = 4.15e-5 / h**2 * T4  # Omega_r h^2 ~ 4.15e-5

        # Baryon-photon ratio R = 3rho_b/(4rho_gamma)
        # R = 31500 * ob_h2 * (T_cmb/2.7)^-4 / (1+z)
        theta = T_cmb / 2.7

        # Drag epoch (Eisenstein-Hu fitting)
        b1 = 0.313*om_h2**(-.419)*(1+.607*om_h2**.674)
        b2 = 0.238*om_h2**.223
        z_d = (1291*om_h2**.251/(1+.659*om_h2**.828)
               * (1+b1*ob_h2**b2))

        # Equality
        z_eq = 2.5e4 * om_h2 * theta**(-4)

        self.log(f"  z_eq  = {z_eq:.0f}")
        self.log(f"  z_drag = {z_d:.0f}")

        # Numerical integration of sound horizon
        # r_d = int_z_d^inf c_s/(H(z)) dz
        # c_s = c/sqrt(3(1+R)) where R = 3rho_b/(4rho_gamma)

        z_arr = np.linspace(z_d, 1e6, 100000)
        a_arr = 1.0 / (1.0 + z_arr)

        # H(z)/H0 = sqrt(Om(1+z)^3 + Or(1+z)^4 + OL)
        # MUST use Omega (not omega_h2) in E(z)!
        Or = 4.15e-5 * T4 / h**2   # Omega_r
        Hz_over_H0 = np.sqrt(Om*(1+z_arr)**3
                             + Or*(1+z_arr)**4 + OL)

        R = 31500 * ob_h2 * theta**(-4) / (1+z_arr)
        c_s = 1.0 / np.sqrt(3*(1+R))  # in units of c

        # r_d = (c/H0) * int dz c_s / E(z)
        # c/H0 = 2997.925/h Mpc
        integrand = c_s / Hz_over_H0
        r_d = (2997.925/h) * _trapz(integrand, z_arr)

        # EH analytical approximation
        k_eq = 7.46e-2*om_h2*theta**(-2)
        R_d = 31500*ob_h2*theta**(-4) / z_d
        R_eq = 31500*ob_h2*theta**(-4) / z_eq
        r_d_EH = ((2/(3*k_eq))*np.sqrt(6/R_eq)
                  * np.log((np.sqrt(1+R_d)+np.sqrt(R_d+R_eq))
                           / (1+np.sqrt(R_eq))))

        # Observed
        r_d_obs = 147.09  # Mpc (Planck 2018)
        r_d_err = 0.26

        self.log(f"\n  r_d (numerical) = {r_d:.2f} Mpc")
        self.log(f"  r_d (EH approx) = {r_d_EH:.2f} Mpc")
        self.log(f"  r_d (Planck)    = {r_d_obs} ± {r_d_err} Mpc")
        pct = (r_d - r_d_obs)/r_d_obs * 100
        self.log(f"  Error (num)     = {pct:+.2f}%")
        self.check("r_d within 5% of Planck", abs(pct) < 5)

        # === BAO observables ===
        self.log(f"\n=== BAO Observables ===\n")

        # D_V(z) = [z D_M^2(z) c / H(z)]^(1/3) / r_d
        # D_M(z) = (c/H0) int_0^z dz'/E(z')
        def D_M(z):
            zz = np.linspace(0, z, 10000)
            Ez = np.sqrt(Om*(1+zz)**3 + Or*(1+zz)**4 + OL)
            return (2997.925/h) * _trapz(1/Ez, zz)

        def D_V(z):
            dm = D_M(z)
            Ez = np.sqrt(Om*(1+z)**3 + Or*(1+z)**4 + OL)
            Hz = 100*h*Ez  # km/s/Mpc
            return (z * dm**2 * 299792.458/Hz)**(1./3)

        self.log(f"  {'z':<6} {'D_V/r_d':>10} {'D_M/r_d':>10}"
                 f" {'D_H/r_d':>10}")
        self.log(f"  {'-'*36}")

        # BAO measurements from BOSS/eBOSS/DESI
        bao_data = [
            (0.15, 4.47, 0.17),   # 6dF
            (0.38, 10.23, 0.17),  # BOSS lowz
            (0.51, 13.36, 0.21),  # BOSS CMASS
            (0.70, 17.86, 0.33),  # eBOSS LRG
            (1.48, 30.69, 0.80),  # eBOSS QSO
            (2.33, 37.6, 1.1),    # eBOSS Lya
        ]

        n_good = 0
        for z, dv_rd_obs, err in bao_data:
            dv = D_V(z)
            dm = D_M(z)
            Ez = np.sqrt(Om*(1+z)**3 + Or*(1+z)**4 + OL)
            dh = 2997.925 / (h * Ez)
            dv_rd = dv / r_d
            dm_rd = dm / r_d
            dh_rd = dh / r_d
            sigma = (dv_rd - dv_rd_obs) / err
            self.log(f"  {z:<6.2f} {dv_rd:>10.2f} {dm_rd:>10.2f}"
                     f" {dh_rd:>10.2f}  (obs:{dv_rd_obs:.2f}"
                     f" {sigma:+.1f}sig)")
            if abs(sigma) < 2:
                n_good += 1

        self.check(f"BAO: {n_good}/{len(bao_data)} within 2sig",
                    n_good >= len(bao_data) - 1)

        # === Angular BAO scale ===
        self.log(f"\n=== Angular BAO ===\n")
        theta_BAO = r_d / D_M(1090) * 180/np.pi  # degrees
        theta_obs = 0.5955  # degrees (Planck)
        self.log(f"  theta_BAO = r_d/D_M(z*) = {theta_BAO:.4f} deg")
        self.log(f"  Planck    = {theta_obs} deg")
        pct_th = (theta_BAO - theta_obs)/theta_obs*100
        self.log(f"  Error     = {pct_th:+.2f}%")

        self.log(f"\n=== Summary ===")
        self.log(f"  r_d = {r_d:.2f} Mpc (Planck: {r_d_obs})")
        self.log(f"  All from DRLT Om, Ob — 0 free parameters.")


if __name__ == "__main__":
    BAOScale().execute()
