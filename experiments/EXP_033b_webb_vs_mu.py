"""
EXP_033b: Webb Dipole vs μ Anti-correlation — Published Data Test
================================================================

DRLT prediction #54: Δα_em and Δμ must have OPPOSITE signs
at the same sky location (ghost sum rule Σδᵢ = 0).

Method:
1. Use Webb dipole model (amplitude, direction) to predict Δα/α
   at each H₂ quasar coordinate
2. Compare sign with published Δμ/μ measurements
3. Anti-correlation → consistent with DRLT
   Same sign    → DRLT falsified

Data sources:
- Webb dipole: King et al. 2012, MNRAS 422, 3370
  Dipole: A = 1.1e-5, direction RA=17.3h Dec=-61°
- Δμ/μ measurements: compilation from Ubachs et al. 2016,
  Rev. Mod. Phys. 88, 021003, and individual papers
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from experiment import Experiment
import numpy as np


# ── Webb dipole model ────────────────────────────────────────

# Dipole parameters from King et al. 2012
DIPOLE_AMP = 1.1e-5  # Δα/α amplitude
DIPOLE_RA_h = 17.3   # hours
DIPOLE_DEC_deg = -61.0  # degrees

# Convert dipole direction to unit vector
DIPOLE_RA_rad = DIPOLE_RA_h * 15 * np.pi / 180  # hours → degrees → radians
DIPOLE_DEC_rad = DIPOLE_DEC_deg * np.pi / 180

DIPOLE_VEC = np.array([
    np.cos(DIPOLE_DEC_rad) * np.cos(DIPOLE_RA_rad),
    np.cos(DIPOLE_DEC_rad) * np.sin(DIPOLE_RA_rad),
    np.sin(DIPOLE_DEC_rad)
])

def webb_dipole_prediction(ra_h, dec_deg):
    """Predict Δα/α at given sky coordinate using Webb dipole model."""
    ra_rad = ra_h * 15 * np.pi / 180
    dec_rad = dec_deg * np.pi / 180
    pos_vec = np.array([
        np.cos(dec_rad) * np.cos(ra_rad),
        np.cos(dec_rad) * np.sin(ra_rad),
        np.sin(dec_rad)
    ])
    cos_angle = np.dot(pos_vec, DIPOLE_VEC)
    return DIPOLE_AMP * cos_angle


# ── Published Δμ/μ measurements from H₂ quasar absorbers ────
# Sources: Ubachs et al. 2016 compilation + individual papers
# Coordinates from quasar names (standard J2000 convention)
# Δμ/μ values from published analyses

H2_DATA = [
    # (name, RA_h, Dec_deg, z_abs, dmu_mu, dmu_err, reference)
    # Quasar names encode approximate coordinates:
    # QHHMM±DDD → RA=HHhMMm, Dec=±DD°

    ("Q0347-383",
     3 + 49/60, -38.18, 3.025,
     2.1e-6, 6.0e-6,
     "Wendt & Molaro 2012"),

    ("Q0405-443",
     4 + 7/60, -44.17, 2.595,
     10.1e-6, 6.2e-6,
     "King+ 2008; Reinhold+ 2006"),

    ("Q0528-250",
     5 + 30/60, -25.03, 2.811,
     0.3e-6, 3.7e-6,
     "King+ 2011"),

    ("Q0642-504",
     6 + 43/60, -50.48, 2.659,
     17.1e-6, 5.8e-6,
     "Bagdonaite+ 2014"),

    ("J1237+0648",
     12 + 37/60, +6.80, 2.688,
     -5.4e-6, 7.2e-6,
     "Dapra+ 2015"),

    ("J2123-0050",
     21 + 23/60, -0.83, 2.059,
     5.6e-6, 6.2e-6,
     "Malec+ 2010; vanWeerdenburg+ 2011"),

    ("Q2348-011",
     23 + 51/60, -0.92, 2.426,
     -6.8e-6, 27.8e-6,
     "Bagdonaite+ 2012"),

    ("B0642-5038",
     6 + 43/60, -50.63, 2.659,
     12.7e-6, 4.5e-6,
     "Albornoz Vasquez+ 2014"),

    ("HE0027-1836",
     0 + 30/60, -18.33, 2.402,
     -7.6e-6, 10.2e-6,
     "Rahmani+ 2013"),

    ("Q1443+2724",
     14 + 46/60, +27.11, 4.224,
     -9.5e-6, 7.6e-6,
     "Bagdonaite+ 2015"),
]


class EXP_033b(Experiment):
    ID = "033b"
    TITLE = "Webb vs Mu Anti-correlation"

    def run(self):
        self.log("=" * 65)
        self.log("Webb Dipole Δα/α vs Published Δμ/μ: Sign Correlation Test")
        self.log("=" * 65)
        self.log("")
        self.log(f"Webb dipole: A = {DIPOLE_AMP:.1e}")
        self.log(f"Direction: RA = {DIPOLE_RA_h}h, Dec = {DIPOLE_DEC_deg} deg")
        self.log("")
        self.log("DRLT prediction: Δα and Δμ must have OPPOSITE signs")
        self.log("(ghost sum rule Σδᵢ = 0 → α_s anti-correlates with α_em)")
        self.log("(μ = m_p/m_e ∝ Λ_QCD ∝ α_s → μ tracks α_s)")
        self.log("")

        header = (f"  {'Quasar':<16s} {'z':>5s} {'Δα/α(pred)':>12s} "
                  f"{'Δμ/μ(obs)':>12s} {'±err':>10s} {'Signs':>7s} {'Anti?':>6s}")
        self.log(header)
        self.log("  " + "-" * 72)

        n_anti = 0  # opposite signs (DRLT prediction)
        n_same = 0  # same signs (would falsify)
        n_ambiguous = 0  # one or both consistent with zero

        predicted_da = []
        observed_dmu = []
        weights = []

        for name, ra, dec, z, dmu, dmu_err, ref in H2_DATA:
            da_pred = webb_dipole_prediction(ra, dec)
            predicted_da.append(da_pred)
            observed_dmu.append(dmu)
            weights.append(1.0 / dmu_err**2)

            # Determine signs
            sign_alpha = "+" if da_pred > 0 else "-"
            sign_mu = "+" if dmu > 0 else ("-" if dmu < 0 else "0")

            # Is |Δμ| > 1σ? (significant)
            significant = abs(dmu) > dmu_err

            if not significant:
                status = "~0"
                n_ambiguous += 1
            elif (da_pred > 0 and dmu < 0) or (da_pred < 0 and dmu > 0):
                status = "YES"
                n_anti += 1
            else:
                status = "NO"
                n_same += 1

            self.log(f"  {name:<16s} {z:5.3f} {da_pred:+12.2e} "
                     f"{dmu:+12.2e} {dmu_err:10.2e} "
                     f"{sign_alpha:>3s}/{sign_mu:<3s} {status:>6s}")

        self.log("")
        self.log(f"  Anti-correlated (DRLT consistent): {n_anti}")
        self.log(f"  Same sign (DRLT inconsistent):     {n_same}")
        self.log(f"  Ambiguous (|Δμ| < 1σ):             {n_ambiguous}")

        # Weighted correlation
        predicted_da = np.array(predicted_da)
        observed_dmu = np.array(observed_dmu)
        weights = np.array(weights)

        w_mean_da = np.average(predicted_da, weights=weights)
        w_mean_dmu = np.average(observed_dmu, weights=weights)
        cov = np.average((predicted_da - w_mean_da) * (observed_dmu - w_mean_dmu),
                         weights=weights)
        var_da = np.average((predicted_da - w_mean_da)**2, weights=weights)
        var_dmu = np.average((observed_dmu - w_mean_dmu)**2, weights=weights)
        if var_da > 0 and var_dmu > 0:
            w_corr = cov / np.sqrt(var_da * var_dmu)
        else:
            w_corr = 0

        self.log("")
        self.log(f"  Weighted Pearson r = {w_corr:+.3f}")
        self.log(f"  (negative = anti-correlation = DRLT consistent)")

        self.log("")
        self.log("=" * 65)
        self.log("INTERPRETATION")
        self.log("=" * 65)
        self.log("")

        if n_same > n_anti and n_same > 2:
            self.log("  *** DRLT TENSION: majority same-sign ***")
            self.log("  Ghost sum rule may be violated.")
        elif n_anti > n_same:
            self.log("  DRLT CONSISTENT: anti-correlation tendency observed")
            self.log("  Ghost sum rule Σδᵢ = 0 is compatible with data.")
        else:
            self.log("  INCONCLUSIVE: data too noisy to distinguish")
            self.log("  Most measurements are consistent with zero.")

        self.log("")
        self.log("  IMPORTANT CAVEATS:")
        self.log("  - Δμ/μ measurements have large uncertainties (~10⁻⁵)")
        self.log("  - Webb Δα/α dipole amplitude is also ~10⁻⁵")
        self.log("  - Individual Δμ/μ values are mostly 1-2σ from zero")
        self.log("  - This is a consistency check, not a definitive test")
        self.log("  - A definitive test requires dedicated observations")
        self.log("    of BOTH α and μ from the SAME quasar sightlines")

        self.check("data loaded and processed", len(H2_DATA) >= 5)
        self.check("anti-correlation count >= same-sign count",
                   n_anti >= n_same)
        self.check("weighted correlation negative or near zero",
                   w_corr < 0.3)

        self.log("")
        self.log("  Prediction for future observations:")
        self.log("  At RA~17h Dec~-61 (toward dipole): Δα > 0, Δμ < 0")
        self.log("  At RA~5h Dec~+61 (away from dipole): Δα < 0, Δμ > 0")
        self.log("")
        self.log("  Free parameters: 0")
        self.log("  Data sources: Webb+ 2011, King+ 2012, Ubachs+ 2016")


if __name__ == "__main__":
    EXP_033b().execute()
