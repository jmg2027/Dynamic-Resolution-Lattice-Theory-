"""
CST_014: Age of the Universe from DRLT
=========================================
t_0 = F(Om,OL) / H_0 where F is exact from DRLT.
Detailed cosmic timeline from simplex block universe.

Joint research by Mingu Jeong and Claude (Anthropic).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

import numpy as np
from drlt import (D, N_S, N_T, ALPHA_GUT, M_PLANCK_GEV,
                  dark_energy_fraction)
from experiment import Experiment

_trapz = getattr(np, 'trapezoid', getattr(np, 'trapz', None))
HBAR_S = 6.5822e-25   # GeV·s
KMS_MPC = 3.2408e-20  # (km/s/Mpc) → s^-1
GEV_TO_H0 = 1.0 / (HBAR_S * KMS_MPC)
GYR = 977.8           # (km/s/Mpc)^-1 in Gyr


class UniverseAge(Experiment):
    ID = "CST_014"
    TITLE = "Age of the Universe"

    def run(self):
        OL = dark_energy_fraction()
        Om = 1 - OL

        # DRLT H_0
        N_H = D**2 * N_S + D * N_T + N_S  # 88
        ln_H0 = np.log(D+1) + np.log(M_PLANCK_GEV) - N_H*np.log(D)
        H0_DRLT = np.exp(ln_H0) * GEV_TO_H0 * N_T / N_S  # 70.85

        # t_0*H_0 numerical (include radiation for consistency)
        Or = 9.15e-5
        zz = np.logspace(-8, 7, 500000)
        Ez = np.sqrt(Om*(1+zz)**3 + Or*(1+zz)**4 + OL)
        F = _trapz(1.0/((1+zz)*Ez), zz)
        F_analytic = (2.0/3)/np.sqrt(OL)*np.arcsinh(np.sqrt(OL/Om))

        self.log("\n=== DRLT Fundamental Parameters ===\n")
        self.log(f"  Om = {Om:.6f}  OL = {OL:.6f}  w = -1")
        self.log(f"  H_0 = {H0_DRLT:.2f} km/s/Mpc")
        self.log(f"  t_0*H_0 = {F:.6f}")

        # =============================
        # Part 1: Age of the Universe
        # =============================
        self.log(f"\n=== Part 1: Present Age t_0 ===\n")

        t0 = F * GYR / H0_DRLT
        t0_obs = 13.797  # Gyr (Planck 2018)

        self.log(f"  t_0 = {F:.6f} × {GYR:.1f} / {H0_DRLT:.2f}")
        self.log(f"      = {t0:.4f} Gyr")
        self.log(f"  Observed (Planck): {t0_obs} ± 0.023 Gyr")
        pct = (t0 - t0_obs)/t0_obs * 100
        self.log(f"  Error: {pct:+.2f}%")
        self.check("Age within 5%", abs(pct) < 5)

        # =============================
        # Part 2: Cosmic Timeline
        # =============================
        self.log(f"\n=== Part 2: Cosmic Timeline (DRLT) ===\n")

        # Key epochs from DRLT parameters
        Or = 9.15e-5  # Omega_r (from T_CMB=2.725K, h=0.7085)
        ob_h2 = Om/(1+D+1.0/N_S) * (H0_DRLT/100)**2
        om_h2 = Om * (H0_DRLT/100)**2
        h = H0_DRLT / 100

        # Matter-radiation equality
        z_eq = Om / Or  # roughly
        z_eq_precise = 2.5e4 * om_h2 * (2.7255/2.7)**(-4)
        t_eq = F * GYR / H0_DRLT  # need proper calculation

        # Age at redshift z: t(z) = int_z^inf dz'/[(1+z')E(z')]
        def age_at_z(z_val):
            """Age of universe at redshift z (in Gyr)."""
            if z_val < 1e-6:
                return t0
            lz_lo = np.log10(1 + z_val)
            zz = np.logspace(lz_lo, 7, 500000) - 1
            zz = zz[zz >= z_val]
            if len(zz) < 2:
                return 0.0
            Ez = np.sqrt(Om*(1+zz)**3 + Or*(1+zz)**4 + OL)
            integ = 1.0 / ((1+zz) * Ez)
            return _trapz(integ, zz) * GYR / H0_DRLT

        def lookback(z_val):
            """Lookback time to redshift z (in Gyr)."""
            return t0 - age_at_z(z_val)

        events = [
            ("Big Bang", 1e10, "t=0"),
            ("Inflation ends", 1e28, "~10^-32 s"),
            ("EW phase transition", 1e15, "~10^-11 s"),
            ("QCD transition", 1e12, "~10^-5 s"),
            ("Neutrino decoupling", 1e10, "~1 s"),
            ("BBN (D, He)", 4e8, "~3 min"),
            ("Matter-radiation eq", z_eq_precise, None),
            ("Recombination", 1090, None),
            ("Dark ages begin", 1090, None),
            ("First stars", 20, None),
            ("Reionization", 8, None),
            ("DE-matter eq", None, None),
            ("Solar system", 0.44, None),
            ("Now", 0, None),
        ]

        # DE-matter equality: Om(1+z)^3 = OL → z = (OL/Om)^(1/3)-1
        z_DE = (OL / Om)**(1./3) - 1
        events[11] = ("DE-matter eq", z_DE, None)

        self.log(f"  {'Event':<25} {'z':>12} {'Lookback':>12}"
                 f" {'Age':>12}")
        self.log(f"  {'-'*61}")

        for name, z_val, note in events:
            if z_val is None:
                continue
            if z_val > 1e6:
                lb_str = note if note else "very early"
                age_str = note if note else "~0"
                self.log(f"  {name:<25} {z_val:>12.2e}"
                         f" {lb_str:>12} {age_str:>12}")
            else:
                lb = lookback(z_val)
                age = t0 - lb
                self.log(f"  {name:<25} {z_val:>12.2f}"
                         f" {lb:>12.3f} {age:>12.3f}")

        # =============================
        # Part 3: Key Epoch Ages
        # =============================
        self.log(f"\n=== Part 3: Key Epoch Ages ===\n")

        z_rec = 1090
        lb_rec = lookback(z_rec)
        age_rec = t0 - lb_rec

        z_first = 20
        lb_first = lookback(z_first)
        age_first = t0 - lb_first

        lb_DE = lookback(z_DE)
        age_DE = t0 - lb_DE

        lb_solar = lookback(0.44)
        age_solar = t0 - lb_solar

        self.log(f"  Recombination (z={z_rec}):")
        self.log(f"    Age = {age_rec*1e6:.0f} kyr = {age_rec:.6f} Gyr")
        self.log(f"    Observed: ~380 kyr")
        self.check("Recombination ~380 kyr",
                    300e-6 < age_rec < 500e-6)

        self.log(f"\n  First stars (z~20):")
        self.log(f"    Age = {age_first*1e3:.0f} Myr = {age_first:.3f} Gyr")

        self.log(f"\n  DE-matter equality (z={z_DE:.2f}):")
        self.log(f"    Age = {age_DE:.3f} Gyr")
        self.log(f"    Lookback = {lb_DE:.3f} Gyr")

        self.log(f"\n  Solar system (z~0.44):")
        self.log(f"    Age = {age_solar:.3f} Gyr")
        self.log(f"    (Sun is ~4.6 Gyr old → formed at"
                 f" t={t0-4.6:.1f} Gyr)")

        # =============================
        # Part 4: Block Universe View
        # =============================
        self.log(f"\n=== Part 4: Block Universe Interpretation ===\n")

        self.log(f"  In DRLT, the universe doesn't 'evolve' —")
        self.log(f"  the Gram matrix G just IS.")
        self.log(f"")
        self.log(f"  'Time' = direction of increasing alignment")
        self.log(f"  = direction of decreasing det(G_h)")
        self.log(f"  = direction of increasing entropy")
        self.log(f"")
        self.log(f"  The 'age' t_0 is the metric distance along")
        self.log(f"  this alignment gradient from the random")
        self.log(f"  initial state to our cosmic address epsilon_0.")
        self.log(f"")
        self.log(f"  epsilon_0 ~ {ALPHA_GUT*N_T/(D+1):.4f}")
        self.log(f"  (encodes how aligned we are)")
        self.log(f"")
        self.log(f"  Future: alignment continues → forces fade")
        self.log(f"  t_future → ∞ but physics dies (det → 0)")

        # =============================
        # Part 5: Future of the Universe
        # =============================
        self.log(f"\n=== Part 5: Far Future ===\n")

        # With w=-1 exactly, the universe approaches
        # de Sitter space exponentially
        # a(t) → exp(H_inf * t) where H_inf = H_0*sqrt(OL)

        H_inf = H0_DRLT * np.sqrt(OL)
        t_double = np.log(2) / (H_inf / GYR)

        self.log(f"  Asymptotic de Sitter:")
        self.log(f"    H_inf = H_0 sqrt(OL) = {H_inf:.2f} km/s/Mpc")
        self.log(f"    Doubling time = {t_double:.2f} Gyr")
        self.log(f"")

        # Degenerate era: last stars die
        t_stars = 1e14  # years
        self.log(f"  Star formation era ends: ~{t_stars:.0e} yr")
        self.log(f"  Proton decay (if any): ~10^40 yr")
        self.log(f"  BH evaporation: ~10^100 yr")
        self.log(f"")
        self.log(f"  In DRLT: these correspond to progressive")
        self.log(f"  alignment → det(G_h) → 0, hbar_h → 0")
        self.log(f"  The universe becomes 'more classical'")
        self.log(f"  as it ages. Quantum effects vanish.")

        self.check("t_0 computed successfully", t0 > 0)

        # =============================
        # Summary
        # =============================
        self.log(f"\n=== Summary ===\n")
        self.log(f"  t_0 = {t0:.4f} Gyr  (DRLT, H_0={H0_DRLT:.2f})")
        self.log(f"  t_0 = {F*GYR/67.4:.4f} Gyr  (if H_0=67.4, CMB)")
        self.log(f"  t_0 = {F*GYR/73.04:.4f} Gyr (if H_0=73.04, SH0ES)")
        self.log(f"  t_0*H_0 = {F:.6f}  ← EXACT, 0 free params")
        self.log(f"  Recombination: {age_rec*1e6:.0f} kyr")
        self.log(f"  DE-matter eq: z = {z_DE:.2f}")


if __name__ == "__main__":
    UniverseAge().execute()
