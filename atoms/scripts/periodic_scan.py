"""
DRLT Periodic Table Scanner — Z=1 to Z=36 (first 3 periods + 3d block)
Compute IE from simplex geometry, compare to observation, find patterns.

Joint research by Mingu Jeong and Claude (Anthropic).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
import drlt

# === Constants ===
Ry = 13.606  # eV (Rydberg)
a = drlt.ALPHA_GUT
d, n_S, n_T = drlt.D, drlt.N_S, drlt.N_T

# === Observed IE (eV) — NIST ===
IE_OBS = {
    1:13.598, 2:24.587, 3:5.392, 4:9.323, 5:8.298,
    6:11.260, 7:14.534, 8:13.618, 9:17.423, 10:21.565,
    11:5.139, 12:7.646, 13:5.986, 14:8.152, 15:10.487,
    16:10.360, 17:12.968, 18:15.760,
    19:4.341, 20:6.113, 21:6.562, 22:6.828, 23:6.746,
    24:6.767, 25:7.434, 26:7.902, 27:7.881, 28:7.640,
    29:7.726, 30:9.394, 31:5.999, 32:7.900, 33:9.789,
    34:9.752, 35:11.814, 36:14.000,
}

SYMBOLS = ['','H','He','Li','Be','B','C','N','O','F','Ne',
           'Na','Mg','Al','Si','P','S','Cl','Ar',
           'K','Ca','Sc','Ti','V','Cr','Mn','Fe','Co','Ni',
           'Cu','Zn','Ga','Ge','As','Se','Br','Kr']

# === Electron configuration ===
CONFIGS = {
    1:'1s1', 2:'1s2', 3:'[He]2s1', 4:'[He]2s2',
    5:'[He]2s2 2p1', 6:'[He]2s2 2p2', 7:'[He]2s2 2p3',
    8:'[He]2s2 2p4', 9:'[He]2s2 2p5', 10:'[He]2s2 2p6',
    11:'[Ne]3s1', 12:'[Ne]3s2', 13:'[Ne]3s2 3p1',
    14:'[Ne]3s2 3p2', 15:'[Ne]3s2 3p3', 16:'[Ne]3s2 3p4',
    17:'[Ne]3s2 3p5', 18:'[Ne]3s2 3p6',
    19:'[Ar]4s1', 20:'[Ar]4s2',
    21:'[Ar]3d1 4s2', 22:'[Ar]3d2 4s2', 23:'[Ar]3d3 4s2',
    24:'[Ar]3d5 4s1', 25:'[Ar]3d5 4s2', 26:'[Ar]3d6 4s2',
    27:'[Ar]3d7 4s2', 28:'[Ar]3d8 4s2', 29:'[Ar]3d10 4s1',
    30:'[Ar]3d10 4s2', 31:'[Ar]3d10 4s2 4p1',
    32:'[Ar]3d10 4s2 4p2', 33:'[Ar]3d10 4s2 4p3',
    34:'[Ar]3d10 4s2 4p4', 35:'[Ar]3d10 4s2 4p5',
    36:'[Ar]3d10 4s2 4p6',
}

# === DRLT Screening Rules ===
# Same-shell: σ_same = 1/n_T + n_T × α_GUT = 0.549
# Inner→outer: σ_inner = 1 - n_S/(d²-1) = 7/8 = 0.875
# He correction: factor (1-4α_GUT)

SIGMA_SAME = 1/n_T + n_T * a          # 0.5486
SIGMA_INNER = 1 - n_S/(d**2 - 1)      # 7/8 = 0.875

def shell_structure(Z):
    """Return [(n, l, n_electrons), ...] for element Z."""
    # Standard Aufbau filling order
    order = [(1,0,2), (2,0,2), (2,1,6), (3,0,2), (3,1,6),
             (4,0,2), (3,2,10), (4,1,6), (5,0,2), (4,2,10)]
    shells = []
    remaining = Z
    for n, l, capacity in order:
        if remaining <= 0:
            break
        n_e = min(capacity, remaining)
        shells.append((n, l, n_e))
        remaining -= n_e
    return shells

def compute_IE(Z):
    """DRLT ionization energy for element Z."""
    shells = shell_structure(Z)

    # Outermost shell
    n_outer, l_outer, ne_outer = shells[-1]

    # Inner electron count
    n_inner = Z - ne_outer

    # Screening from inner shells
    sigma_inner_total = n_inner * SIGMA_INNER

    # Screening from same-shell electrons
    sigma_same_total = (ne_outer - 1) * SIGMA_SAME / n_outer

    # Effective nuclear charge
    Z_eff = Z - sigma_inner_total - sigma_same_total
    Z_eff = max(Z_eff, 0.1)

    # IE = Z_eff² × Ry / n²
    # With He-like correction for filled s-subshell
    IE = Z_eff**2 * Ry / n_outer**2

    # Apply (1-4α) correction for paired electrons in same orbital
    if ne_outer >= 2 and l_outer == 0:
        IE *= (1 - 4*a)

    return IE, Z_eff, n_outer, shells

# === Run full scan ===
print("=" * 85)
print("DRLT PERIODIC TABLE: Z=1 to Z=36")
print(f"σ_same = {SIGMA_SAME:.4f}, σ_inner = {SIGMA_INNER:.4f}")
print("=" * 85)

print(f"{'Z':>3} {'Sym':>3} {'n':>2} {'Z_eff':>6} {'IE_drlt':>8} {'IE_obs':>8} "
      f"{'err%':>7} {'config':>15}")
print("-" * 85)

results = []
for Z in range(1, 37):
    IE_drlt, Z_eff, n_out, shells = compute_IE(Z)
    IE_obs = IE_OBS.get(Z, 0)
    err = (IE_drlt - IE_obs) / IE_obs * 100 if IE_obs > 0 else 0
    sym = SYMBOLS[Z] if Z < len(SYMBOLS) else f'{Z}'
    config = CONFIGS.get(Z, '')

    marker = '✓' if abs(err) < 5 else '○' if abs(err) < 15 else '✗'
    print(f"{Z:3d} {sym:>3} {n_out:>2} {Z_eff:6.3f} {IE_drlt:8.3f} {IE_obs:8.3f} "
          f"{err:+7.1f}% {marker} {config:>15}")

    results.append({
        'Z': Z, 'sym': sym, 'IE_drlt': IE_drlt, 'IE_obs': IE_obs,
        'err': err, 'Z_eff': Z_eff, 'n': n_out
    })

# === Statistics ===
errors = [abs(r['err']) for r in results if r['IE_obs'] > 0]
print(f"\n{'='*85}")
print(f"Statistics:")
print(f"  < 5%:  {sum(1 for e in errors if e < 5)}/36")
print(f"  < 15%: {sum(1 for e in errors if e < 15)}/36")
print(f"  < 30%: {sum(1 for e in errors if e < 30)}/36")
print(f"  Median error: {np.median(errors):.1f}%")
print(f"  Mean error:   {np.mean(errors):.1f}%")

# === Save results ===
with open('atoms/results/IE_scan_Z1_36.csv', 'w') as f:
    f.write('Z,sym,n,Z_eff,IE_drlt,IE_obs,err_pct\n')
    for r in results:
        f.write(f"{r['Z']},{r['sym']},{r['n']},{r['Z_eff']:.4f},"
                f"{r['IE_drlt']:.4f},{r['IE_obs']:.4f},{r['err']:.2f}\n")
print(f"\nSaved: atoms/results/IE_scan_Z1_36.csv")

# === Period patterns ===
print(f"\n{'='*85}")
print(f"Period patterns (noble gas IE):")
nobles = [(2,'He'), (10,'Ne'), (18,'Ar'), (36,'Kr')]
for Z, sym in nobles:
    r = results[Z-1]
    print(f"  {sym:>3} (Z={Z:2d}): IE_drlt={r['IE_drlt']:8.3f}, "
          f"IE_obs={r['IE_obs']:8.3f}, err={r['err']:+.1f}%")
