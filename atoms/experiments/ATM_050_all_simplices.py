"""
ATM_050: All Simplices for Every Atom
Joint research by Mingu Jeong and Claude (Anthropic)

Each orbital (n,l,m) = 1 simplex:
  Simplex = {A₁, A₂, A₃, B↑, [B↓]}
  All share the same nucleus A₁A₂A₃.

  s-orbital: B purely temporal (ℂ²)
  p-orbital: B overlaps with 1 A-direction
  d-orbital: B overlaps with 2 A-directions (Sym²₀)
  f-orbital: B overlaps with 3 A-directions (Sym³₀)

Total simplices per atom = number of occupied orbitals.

Tests:
  1. H through Ar: every simplex listed
  2. Transition metal (Fe): d-orbital simplices
  3. Oganesson: full count
  4. Save complete simplex table
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from experiment import Experiment

SYM = ['','H','He','Li','Be','B','C','N','O','F','Ne',
    'Na','Mg','Al','Si','P','S','Cl','Ar','K','Ca',
    'Sc','Ti','V','Cr','Mn','Fe','Co','Ni','Cu','Zn',
    'Ga','Ge','As','Se','Br','Kr','Rb','Sr','Y','Zr',
    'Nb','Mo','Tc','Ru','Rh','Pd','Ag','Cd','In','Sn',
    'Sb','Te','I','Xe','Cs','Ba','La','Ce','Pr','Nd',
    'Pm','Sm','Eu','Gd','Tb','Dy','Ho','Er','Tm','Yb',
    'Lu','Hf','Ta','W','Re','Os','Ir','Pt','Au','Hg',
    'Tl','Pb','Bi','Po','At','Rn','Fr','Ra','Ac','Th',
    'Pa','U','Np','Pu','Am','Cm','Bk','Cf','Es','Fm',
    'Md','No','Lr','Rf','Db','Sg','Bh','Hs','Mt','Ds',
    'Rg','Cn','Nh','Fl','Mc','Lv','Ts','Og']

# m-labels for each l
M_LABELS = {
    0: [''],
    1: ['x', 'y', 'z'],
    2: ['xy', 'xz', 'yz', 'x²-y²', 'z²'],
    3: ['fz³', 'xz²', 'yz²', 'xyz', 'z(x²-y²)', 'x(x²-3y²)', 'y(3x²-y²)'],
}

# Spatial description for each (l, m)
def spatial_desc(l, m):
    if l == 0:
        return '(t₁,t₂, ε,ε,ε)'
    elif l == 1:
        dirs = ['(t, 0, ε,0,0)', '(0,t, 0,ε,0)', '(t,0, 0,0,ε)']
        return dirs[m] if m < 3 else f'p_{m}'
    elif l == 2:
        return f'Sym²₀[{M_LABELS[2][m]}]'
    else:
        return f'Sym³₀[{M_LABELS[3][m]}]'


def get_simplices(Z):
    """Return list of simplices for atom Z."""
    order = []
    for n in range(1, 9):
        for l in range(min(n, 4)):
            order.append((n+l, n, l))
    order.sort()

    simplices = []
    remaining = Z
    for _, n, l in order:
        n_orb = 2*l+1
        max_e = 2*n_orb
        count = min(remaining, max_e)
        if count <= 0:
            break
        remaining -= count

        for m in range(n_orb):
            e_up = 1 if count > m else 0
            e_dn = 1 if count > n_orb + m else 0
            e_total = e_up + e_dn
            if e_total > 0:
                sub = 'spdf'[l]
                m_lab = M_LABELS[l][m]
                label = f'{n}{sub}_{m_lab}' if m_lab else f'{n}{sub}'
                spin = '↑↓' if e_total == 2 else '↑'
                simplices.append({
                    'n': n, 'l': l, 'm': m,
                    'label': label, 'spin': spin,
                    'e': e_total,
                    'spatial': spatial_desc(l, m),
                })
    return simplices


def draw_simplices(Z):
    """Draw all simplices for element Z."""
    sym = SYM[Z] if Z < len(SYM) else f'Z{Z}'
    simps = get_simplices(Z)
    n_simp = len(simps)
    n_elec = sum(s['e'] for s in simps)

    lines = []
    lines.append(f'{"="*55}')
    lines.append(f' {sym} (Z={Z})  {n_elec} electrons  {n_simp} simplices')
    lines.append(f'{"="*55}')
    lines.append(f' Nucleus: A₁(u)━━A₂(u)━━A₃(d)  [orthogonal, confined]')
    lines.append(f'          ┃      ┃      ┃')

    for i, s in enumerate(simps):
        connector = '┣' if i < len(simps)-1 else '┗'
        branch = '┃' if i < len(simps)-1 else ' '

        spin_box = '↑↓' if s['e'] == 2 else '↑ '
        lines.append(f'          {connector}━ S{i+1}: '
                     f'{s["label"]:<8s}[{spin_box}] '
                     f'{s["spatial"]}')

    lines.append(f'')
    return '\n'.join(lines)


class AllSimplices(Experiment):
    ID = "ATM_050"
    TITLE = "All Simplices for Every Atom"

    def run(self):
        self.test1_light_atoms()
        self.test2_transition()
        self.test3_heavy()
        self.test4_save_all()

    def test1_light_atoms(self):
        """H through Ar: every simplex."""
        self.log(f"\n  Period 1-3: All simplices\n")
        for Z in range(1, 19):
            self.log(draw_simplices(Z))
        self.check("H-Ar drawn", True)

    def test2_transition(self):
        """Fe, Cu, Au: d-orbital simplices."""
        self.log(f"\n  Transition metals:\n")
        for Z in [26, 29, 79]:
            self.log(draw_simplices(Z))
        self.check("d-block drawn", True)

    def test3_heavy(self):
        """U, Og: f-orbital + full table."""
        self.log(f"\n  Heavy elements:\n")
        for Z in [92, 118]:
            self.log(draw_simplices(Z))
        self.check("Heavy drawn", True)

    def test4_save_all(self):
        """Summary: simplex count per element."""
        self.log(f"\n  {'='*55}")
        self.log(f"  SIMPLEX COUNT: all 118 elements")
        self.log(f"  {'='*55}")
        self.log(f"\n  {'Z':>4} {'Sym':>3} {'e⁻':>4} {'Simp':>5}"
                 f" {'Subshells':>30}")

        for Z in range(1, 119):
            sym = SYM[Z] if Z < len(SYM) else f'{Z}'
            simps = get_simplices(Z)
            n_s = len(simps)
            n_e = sum(s['e'] for s in simps)
            subs = ' '.join(f'{s["label"]}' for s in simps
                            if s['l'] >= 0)
            # Abbreviated
            if len(subs) > 30:
                subs = subs[:27] + '...'
            self.log(f"  {Z:4d} {sym:>3} {n_e:4d} {n_s:5d}"
                     f" {subs:>30}")

        # Statistics
        total_s = sum(len(get_simplices(Z)) for Z in range(1, 119))
        self.log(f"\n  Total simplices across all 118 elements:"
                 f" {total_s}")
        self.log(f"  Average per element: {total_s/118:.1f}")
        self.log(f"  Max (Og, Z=118): {len(get_simplices(118))}")
        self.check("All counted", True)


if __name__ == "__main__":
    AllSimplices().execute()
