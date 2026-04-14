"""
DRLT Representation Framework — Computation IS Visualization
=============================================================

In DRLT, drawing a simplex IS computing its physics.

  Edge thickness = |G_ij|      (metric strength)
  Edge color     = φ_ij        (gauge connection)
  Face shading   = det(G_h)    (hinge area → force strength)
  Face type      = SSS/SST/STT (which force)
  Vertex color   = S(red)/T(blue) (spatial/temporal sector)

There is no separate "visualization" step.
The diagram IS the physical object.

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.patches import FancyArrowPatch
from itertools import combinations
import drlt


# ═══════════════════════════════════════════════════════════════
#  REPRESENTATION: Unified computation + visualization
# ═══════════════════════════════════════════════════════════════

# Color scheme derived from theory
COLORS = {
    'S': '#e74c3c',          # spatial vertex (ℂ³) — red
    'T': '#3498db',          # temporal vertex (ℂ²) — blue
    'SSS': '#e74c3c33',      # strong hinge — red, translucent
    'SST': '#9b59b633',      # EM hinge — purple, translucent
    'STT': '#3498db33',      # weak hinge — blue, translucent
    'edge_ST': '#bdc3c7',    # cross-sector edge — grey
    'edge_SS': '#e74c3caa',  # spatial edge — red
    'edge_TT': '#3498dbaa',  # temporal edge — blue
    'bond': '#27ae60',       # covalent bond (shared T) — green
    'slot': '#bdc3c7',       # empty T slot — grey
    'electron': '#3498db',   # occupied T — blue
}

# Standard vertex layout: pentagon with (S₁,S₂,S₃) top-left-bottom, (T₁,T₂) right
PENTAGON_LAYOUT = {
    0: (0.0, 1.0),     # T₁ (temporal)
    1: (0.95, 0.31),   # T₂ (temporal)
    2: (0.59, -0.81),  # S₁ (spatial)
    3: (-0.59, -0.81), # S₂ (spatial)
    4: (-0.95, 0.31),  # S₃ (spatial)
}

# Physics layout: S on left triangle, T on right
PHYSICS_LAYOUT = {
    0: (1.5, 0.8),     # T₁
    1: (1.5, -0.8),    # T₂
    2: (-0.5, 1.2),    # S₁
    3: (-1.2, 0.0),    # S₂
    4: (-0.5, -1.2),   # S₃
}


class SimplexRepr:
    """
    Unified representation of a 4-simplex.

    This object IS the simplex. Reading its properties computes physics.
    Drawing it visualizes the same physics. No separation.
    """

    VERTEX_NAMES = ['T₁', 'T₂', 'S₁', 'S₂', 'S₃']
    SECTOR = ['T', 'T', 'S', 'S', 'S']

    def __init__(self, simplex: drlt.Simplex = None, psi: np.ndarray = None):
        if simplex is not None:
            self.simplex = simplex
        elif psi is not None:
            self.simplex = drlt.Simplex(psi)
        else:
            self.simplex = drlt.Simplex.random()

        self.G = self.simplex.G
        self._compute_all()

    def _compute_all(self):
        """Compute all properties from G. This IS the physics."""
        # Edges: 10 edges, each with |G|, W, phase
        self.edges = {}
        for i, j in combinations(range(5), 2):
            g = self.G[i, j]
            self.edges[(i, j)] = {
                'G': g,
                'abs': float(np.abs(g)),
                'W': float(np.abs(g)**2 / drlt.D),
                'phase': float(np.angle(g)),
                'type': self._edge_type(i, j),
            }

        # Hinges: 10 triangles, each with det, area, type
        self.hinges = {}
        for tri in combinations(range(5), 3):
            det_val = self.simplex.hinge_det(tri)
            n_T = sum(1 for v in tri if v < drlt.N_T)
            htype = ['SSS', 'SST', 'STT'][min(n_T, 2)]
            self.hinges[tri] = {
                'det': det_val,
                'area': np.sqrt(max(0, det_val)),
                'type': htype,
                'force': {'SSS': 'strong', 'SST': 'EM', 'STT': 'weak'}[htype],
            }

    def _edge_type(self, i, j):
        si, sj = self.SECTOR[i], self.SECTOR[j]
        if si == sj == 'S': return 'SS'
        if si == sj == 'T': return 'TT'
        return 'ST'

    # ── Physics readout (= reading the diagram) ──────────

    def strong_coupling(self) -> float:
        """Read the SSS hinge → strong force strength."""
        sss = [h for h in self.hinges.values() if h['type'] == 'SSS']
        return sum(h['det'] for h in sss)

    def em_coupling(self) -> float:
        """Read the SST hinges → EM force strength."""
        sst = [h for h in self.hinges.values() if h['type'] == 'SST']
        return sum(h['det'] for h in sst)

    def weak_coupling(self) -> float:
        """Read the STT hinges → weak force strength."""
        stt = [h for h in self.hinges.values() if h['type'] == 'STT']
        return sum(h['det'] for h in stt)

    def hinge_census(self) -> dict:
        """Count hinges by type: SSS, SST, STT."""
        census = {'SSS': 0, 'SST': 0, 'STT': 0}
        for h in self.hinges.values():
            census[h['type']] += 1
        return census

    def total_action(self) -> float:
        """Regge action S = Σ A_h δ_h."""
        return self.simplex.regge_action()

    # ── Visualization (= drawing the computation) ────────

    def draw(self, ax=None, layout='physics', title=None,
             show_labels=True, show_values=True,
             occupancy=None, label_map=None):
        """
        Draw this simplex. Every visual property comes from G.

        Args:
            layout: 'physics' or 'pentagon'
            occupancy: dict {vertex_idx: 'electron'|'slot'|'quark'|None}
            label_map: dict {vertex_idx: str} for custom labels
        """
        if ax is None:
            fig, ax = plt.subplots(1, 1, figsize=(6, 6))
        else:
            fig = ax.figure

        pos = PHYSICS_LAYOUT if layout == 'physics' else PENTAGON_LAYOUT

        # 1. Draw hinges (faces) — shading = det(G_h)
        for tri, hdata in self.hinges.items():
            if hdata['det'] > 0.01:
                triangle = plt.Polygon(
                    [pos[v] for v in tri],
                    alpha=min(0.4, hdata['det'] * 0.6),
                    facecolor=COLORS[hdata['type']],
                    edgecolor='none'
                )
                ax.add_patch(triangle)

        # 2. Draw edges — width = |G_ij|, color = sector type
        for (i, j), edata in self.edges.items():
            color = COLORS[f"edge_{edata['type']}"]
            lw = 1 + edata['abs'] * 3
            ax.plot([pos[i][0], pos[j][0]],
                    [pos[i][1], pos[j][1]],
                    color=color, linewidth=lw, zorder=2)
            if show_values:
                mx = (pos[i][0] + pos[j][0]) / 2
                my = (pos[i][1] + pos[j][1]) / 2
                ax.text(mx, my, f'{edata["W"]:.2f}',
                        fontsize=6, ha='center', color='gray', zorder=5)

        # 3. Draw vertices — color = sector
        for v in range(5):
            color = COLORS[self.SECTOR[v]]
            if occupancy and v in occupancy:
                if occupancy[v] == 'slot':
                    color = COLORS['slot']
                elif occupancy[v] == 'bond':
                    color = COLORS['bond']
            ax.plot(pos[v][0], pos[v][1], 'o', color=color,
                    markersize=18, zorder=10, markeredgecolor='white',
                    markeredgewidth=2)
            if show_labels:
                label = label_map[v] if label_map else self.VERTEX_NAMES[v]
                ax.text(pos[v][0], pos[v][1], label,
                        fontsize=8, ha='center', va='center',
                        color='white', fontweight='bold', zorder=11)

        # 4. Formatting
        ax.set_xlim(-2, 2.5)
        ax.set_ylim(-1.8, 1.8)
        ax.set_aspect('equal')
        ax.axis('off')
        if title:
            ax.set_title(title, fontsize=14, fontweight='bold')

        return fig, ax

    def draw_with_physics(self, ax=None, title=None):
        """Draw simplex with physics annotation panel."""
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 6),
                                        gridspec_kw={'width_ratios': [2, 1]})
        self.draw(ax=ax1, title=title or "4-Simplex")

        # Physics panel
        census = self.hinge_census()
        lines = [
            "─── Physics Readout ───",
            f"Hinges: {census['SSS']} SSS + {census['SST']} SST + {census['STT']} STT",
            f"",
            f"Strong: Σdet(SSS) = {self.strong_coupling():.4f}",
            f"EM:     Σdet(SST) = {self.em_coupling():.4f}",
            f"Weak:   Σdet(STT) = {self.weak_coupling():.4f}",
            f"",
            f"Regge action = {self.total_action():.4f}",
            f"",
            f"─── Derived Constants ───",
            f"d={drlt.D}, n_S={drlt.N_S}, n_T={drlt.N_T}",
            f"α_GUT = {drlt.ALPHA_GUT:.5f}",
            f"Binet-Cauchy: 1+12+12=25=d²",
        ]
        ax2.axis('off')
        ax2.text(0.05, 0.95, '\n'.join(lines),
                 transform=ax2.transAxes, fontsize=10,
                 verticalalignment='top', fontfamily='monospace')
        fig.tight_layout()
        return fig


# ═══════════════════════════════════════════════════════════════
#  ATOM RENDERER: Atoms as simplex occupancy patterns
# ═══════════════════════════════════════════════════════════════

class AtomRepr:
    """
    An atom = simplex(es) with specific vertex occupancy.

    Hydrogen: 1 simplex, T₁=electron, T₂=slot
    Helium:   1 simplex, T₁=T₂=electron (fully occupied)
    Lithium:  2 simplices sharing SSS core
    """

    ATOMS = {
        'H':  {'n_simplex': 1, 'electrons': 1, 'name': 'Hydrogen'},
        'He': {'n_simplex': 1, 'electrons': 2, 'name': 'Helium'},
        'Li': {'n_simplex': 2, 'electrons': 3, 'name': 'Lithium'},
        'Be': {'n_simplex': 2, 'electrons': 4, 'name': 'Beryllium'},
        'H2': {'n_simplex': 2, 'electrons': 2, 'name': 'H₂ Molecule',
               'bond': True},
    }

    def __init__(self, element: str):
        assert element in self.ATOMS, f"Unknown: {element}"
        self.element = element
        self.info = self.ATOMS[element]

    def draw(self, figsize=(8, 6)):
        """Draw atom as simplex occupancy diagram."""
        fig, ax = plt.subplots(figsize=figsize)
        info = self.info

        if info['n_simplex'] == 1:
            s = SimplexRepr()
            occ = {}
            if info['electrons'] >= 1: occ[0] = 'electron'
            if info['electrons'] >= 2: occ[1] = 'electron'
            if info['electrons'] < 2:  occ[1] = 'slot'
            s.draw(ax=ax, occupancy=occ,
                   title=f"{info['name']} ({self.element})\n1 simplex")
        else:
            ax.text(0.5, 0.5,
                    f"{info['name']}: {info['n_simplex']} simplices\n"
                    f"(multi-simplex rendering)",
                    ha='center', va='center', fontsize=14,
                    transform=ax.transAxes)
            ax.axis('off')

        census = SimplexRepr().hinge_census()
        ax.text(0.02, 0.02,
                f"10 hinges: {census['SSS']} SSS + {census['SST']} SST + {census['STT']} STT",
                transform=ax.transAxes, fontsize=8, color='gray')

        fig.tight_layout()
        return fig


# ═══════════════════════════════════════════════════════════════
#  CONVENIENCE FUNCTIONS
# ═══════════════════════════════════════════════════════════════

def draw_simplex(psi=None, title="4-Simplex", save=None):
    """Quick: draw a simplex with physics panel."""
    sr = SimplexRepr(psi=psi) if psi is not None else SimplexRepr()
    fig = sr.draw_with_physics(title=title)
    if save:
        fig.savefig(save, dpi=150, bbox_inches='tight')
    return fig

def draw_atom(element, save=None):
    """Quick: draw an atom."""
    fig = AtomRepr(element).draw()
    if save:
        fig.savefig(save, dpi=150, bbox_inches='tight')
    return fig
