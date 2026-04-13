"""
Simplex Atom Diagrams — Visual representation of atomic structures in DRLT
==========================================================================

Each atom = Z simplices sharing an SSS core (nucleus).
Each simplex has 5 vertices: 3 Spatial (S) + 2 Temporal (T).

Vertices:  S = proton/quark (C³)
           T = electron/slot (C²)
Hinges:    SSS = strong, SST = EM, STT = weak

Output: PNG diagrams showing vertices, edges, and hinge types.
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch
from itertools import combinations
import os

# Colors
C_S = '#E74C3C'   # red for S (spatial/quark)
C_T = '#3498DB'   # blue for T (temporal/electron)
C_T_EMPTY = '#85C1E9'  # light blue for empty T slot
C_SSS = '#E74C3C33'   # transparent red
C_SST = '#9B59B633'   # transparent purple
C_STT = '#3498DB33'   # transparent blue
C_BOND = '#2ECC71'    # green for covalent bond

FIGSIZE = (10, 8)


def draw_simplex_edges(ax, positions, vertex_types, alpha=0.15):
    """Draw all edges of a simplex."""
    indices = list(positions.keys())
    for i, j in combinations(indices, 2):
        ti = vertex_types[i]
        tj = vertex_types[j]
        x = [positions[i][0], positions[j][0]]
        y = [positions[i][1], positions[j][1]]
        # Color by type pair
        if ti == 'S' and tj == 'S':
            color = '#E74C3C'
        elif ti == 'T' and tj == 'T':
            color = '#3498DB'
        else:
            color = '#9B59B6'
        ax.plot(x, y, '-', color=color, alpha=alpha, linewidth=1.5, zorder=1)


def draw_hinge_triangle(ax, p1, p2, p3, color, alpha=0.12):
    """Draw a filled triangle for a hinge."""
    tri = plt.Polygon([p1, p2, p3], alpha=alpha, color=color, zorder=0)
    ax.add_patch(tri)


def draw_vertices(ax, positions, vertex_types, labels=None, size=300):
    """Draw vertices with type-based colors."""
    for idx, pos in positions.items():
        vtype = vertex_types[idx]
        color = C_S if vtype == 'S' else C_T
        marker = 'o'
        ax.scatter(*pos, c=color, s=size, zorder=5, edgecolors='black', linewidth=1.5, marker=marker)
        if labels and idx in labels:
            ax.annotate(labels[idx], pos, fontsize=11, ha='center', va='center',
                       fontweight='bold', color='white', zorder=6)


def draw_simplex_boundary(ax, positions, color='gray', linestyle='--', alpha=0.3):
    """Draw the boundary of a simplex (convex hull of its vertices)."""
    pts = np.array(list(positions.values()))
    from matplotlib.path import Path
    # Simple: connect all in order of angle from centroid
    cx, cy = pts.mean(axis=0)
    angles = np.arctan2(pts[:, 1] - cy, pts[:, 0] - cx)
    order = np.argsort(angles)
    ordered = pts[order]
    poly = plt.Polygon(ordered, fill=False, edgecolor=color, linestyle=linestyle,
                       alpha=alpha, linewidth=2, zorder=0)
    ax.add_patch(poly)


# ═══════════════════════════════════════════════════════════════
#  Individual atom diagrams
# ═══════════════════════════════════════════════════════════════

def diagram_hydrogen(ax):
    """Hydrogen: 1 simplex, 5 vertices."""
    ax.set_title('Hydrogen (H)\n1 simplex', fontsize=14, fontweight='bold')

    # Pentagon layout
    angles = [np.pi/2 + 2*np.pi*k/5 for k in range(5)]
    r = 2.0
    positions = {}
    # S vertices at top-left, top-right, bottom
    positions[0] = (r*np.cos(angles[0]), r*np.sin(angles[0]))  # S₁ top
    positions[1] = (r*np.cos(angles[1]), r*np.sin(angles[1]))  # S₂
    positions[2] = (r*np.cos(angles[2]), r*np.sin(angles[2]))  # S₃
    positions[3] = (r*np.cos(angles[3]), r*np.sin(angles[3]))  # T₁ electron
    positions[4] = (r*np.cos(angles[4]), r*np.sin(angles[4]))  # T₂ slot

    vtypes = {0: 'S', 1: 'S', 2: 'S', 3: 'T', 4: 'T'}
    labels = {0: 'S₁', 1: 'S₂', 2: 'S₃', 3: 'T₁', 4: 'T₂'}

    # Draw hinge triangles (key ones)
    # SSS hinge (strong force)
    draw_hinge_triangle(ax, positions[0], positions[1], positions[2], '#E74C3C', 0.15)
    # A few SST hinges
    draw_hinge_triangle(ax, positions[0], positions[1], positions[3], '#9B59B6', 0.08)
    draw_hinge_triangle(ax, positions[1], positions[2], positions[3], '#9B59B6', 0.08)

    draw_simplex_edges(ax, positions, vtypes, alpha=0.3)
    draw_vertices(ax, positions, vtypes, labels)

    # Annotations
    ax.annotate('SSS\n(strong)', xy=(0, 1.2), fontsize=9, ha='center',
               color='#E74C3C', fontweight='bold')
    ax.annotate('electron', xy=positions[3], xytext=(positions[3][0]-1.5, positions[3][1]-0.8),
               fontsize=9, color='#3498DB', arrowprops=dict(arrowstyle='->', color='#3498DB'))
    ax.annotate('slot', xy=positions[4], xytext=(positions[4][0]+1.5, positions[4][1]-0.8),
               fontsize=9, color='#85C1E9', arrowprops=dict(arrowstyle='->', color='#85C1E9'))

    # Hinge count
    ax.text(0, -3.2, '10 hinges: 1 SSS + 6 SST + 3 STT',
            ha='center', fontsize=9, style='italic')


def diagram_helium(ax):
    """Helium: 2 simplices sharing SSS core."""
    ax.set_title('Helium (He)\n2 simplices, shared SSS', fontsize=14, fontweight='bold')

    # SSS core at center, T vertices spread out
    positions = {
        0: (0, 1.5),     # S₁
        1: (-1.3, -0.5), # S₂
        2: (1.3, -0.5),  # S₃
        3: (-2.5, 2.0),  # T₁ (e₁↑)
        4: (-2.5, -2.0), # T₂ (slot₁)
        5: (2.5, 2.0),   # T₃ (e₂↓)
        6: (2.5, -2.0),  # T₄ (slot₂)
    }
    vtypes = {0: 'S', 1: 'S', 2: 'S', 3: 'T', 4: 'T', 5: 'T', 6: 'T'}
    labels = {0: 'S₁', 1: 'S₂', 2: 'S₃', 3: 'T₁', 4: 'T₂', 5: 'T₃', 6: 'T₄'}

    # SSS hinge (shared nucleus)
    draw_hinge_triangle(ax, positions[0], positions[1], positions[2], '#E74C3C', 0.2)

    # Simplex A edges (S + T₁,T₂)
    simpA = {k: positions[k] for k in [0,1,2,3,4]}
    simpB = {k: positions[k] for k in [0,1,2,5,6]}
    draw_simplex_edges(ax, simpA, vtypes, alpha=0.2)
    draw_simplex_edges(ax, simpB, vtypes, alpha=0.2)

    draw_vertices(ax, positions, vtypes, labels)

    # Simplex labels
    ax.annotate('Simplex A', xy=(-1.8, 0.5), fontsize=10, color='gray',
               fontweight='bold', style='italic')
    ax.annotate('Simplex B', xy=(1.0, 0.5), fontsize=10, color='gray',
               fontweight='bold', style='italic')
    ax.annotate('SSS\n(shared nucleus)', xy=(0, 0.1), fontsize=9,
               ha='center', color='#E74C3C', fontweight='bold')

    ax.text(0, -3.5, '19 hinges total (SSS shared between both simplices)',
            ha='center', fontsize=9, style='italic')


def diagram_h2_molecule(ax):
    """H₂: 2 simplices sharing T vertex (covalent bond)."""
    ax.set_title('H₂ Molecule\n2 simplices, shared T (bond)', fontsize=14, fontweight='bold')

    positions = {
        # Proton A (left)
        0: (-3, 1.2),    # S₁
        1: (-4, -0.5),   # S₂
        2: (-2, -0.5),   # S₃
        # Proton B (right)
        3: (3, 1.2),     # S₄
        4: (2, -0.5),    # S₅
        5: (4, -0.5),    # S₆
        # T vertices
        6: (-3, -2.0),   # T₁
        7: (0, 0),       # T_shared (BOND!)
        8: (3, -2.0),    # T₂
    }
    vtypes = {i: 'S' for i in range(6)}
    vtypes.update({6: 'T', 7: 'T', 8: 'T'})
    labels = {0: 'S₁', 1: 'S₂', 2: 'S₃', 3: 'S₄', 4: 'S₅', 5: 'S₆',
              6: 'T₁', 7: 'T*', 8: 'T₂'}

    # SSS hinges
    draw_hinge_triangle(ax, positions[0], positions[1], positions[2], '#E74C3C', 0.15)
    draw_hinge_triangle(ax, positions[3], positions[4], positions[5], '#E74C3C', 0.15)

    # Simplex edges
    simpA = {k: positions[k] for k in [0,1,2,6,7]}
    simpB = {k: positions[k] for k in [3,4,5,7,8]}
    draw_simplex_edges(ax, simpA, vtypes, alpha=0.2)
    draw_simplex_edges(ax, simpB, vtypes, alpha=0.2)

    # Highlight the shared vertex
    ax.scatter(*positions[7], c=C_BOND, s=400, zorder=5, edgecolors='black',
              linewidth=2, marker='D')
    ax.annotate('T*', positions[7], fontsize=11, ha='center', va='center',
               fontweight='bold', color='white', zorder=6)

    # Draw other vertices
    for idx in [0,1,2,3,4,5,6,8]:
        color = C_S if vtypes[idx] == 'S' else C_T
        ax.scatter(*positions[idx], c=color, s=300, zorder=5, edgecolors='black',
                  linewidth=1.5)
        ax.annotate(labels[idx], positions[idx], fontsize=11, ha='center', va='center',
                   fontweight='bold', color='white', zorder=6)

    ax.annotate('covalent bond\n(shared T vertex)', xy=positions[7],
               xytext=(0, -2.5), fontsize=9, ha='center', color=C_BOND,
               fontweight='bold',
               arrowprops=dict(arrowstyle='->', color=C_BOND))
    ax.text(0, -3.5, 'Proton A + Proton B share one temporal vertex',
            ha='center', fontsize=9, style='italic')


def diagram_lithium(ax):
    """Lithium: 3 simplices sharing SSS core."""
    ax.set_title('Lithium (Li)\n3 simplices, shared SSS', fontsize=14, fontweight='bold')

    # SSS core at center
    positions = {
        0: (0, 1.2),     # S₁
        1: (-1.0, -0.3), # S₂
        2: (1.0, -0.3),  # S₃
    }
    # 3 pairs of T vertices, evenly spaced around
    t_angles = [np.pi/2, np.pi/2 + 2*np.pi/3, np.pi/2 + 4*np.pi/3]
    r_inner, r_outer = 2.5, 3.2
    for k in range(3):
        a = t_angles[k]
        positions[3 + 2*k] = (r_inner * np.cos(a - 0.15), r_inner * np.sin(a - 0.15))
        positions[3 + 2*k + 1] = (r_outer * np.cos(a + 0.15), r_outer * np.sin(a + 0.15))

    vtypes = {0: 'S', 1: 'S', 2: 'S'}
    for k in range(6):
        vtypes[3+k] = 'T'

    labels = {0: 'S₁', 1: 'S₂', 2: 'S₃',
              3: 'T₁', 4: 'T₂', 5: 'T₃', 6: 'T₄', 7: 'T₅', 8: 'T₆'}

    # SSS core
    draw_hinge_triangle(ax, positions[0], positions[1], positions[2], '#E74C3C', 0.25)

    # Simplex edges
    for k in range(3):
        simp = {0: positions[0], 1: positions[1], 2: positions[2],
                3+2*k: positions[3+2*k], 3+2*k+1: positions[3+2*k+1]}
        # Just draw T-to-S edges
        for s in [0,1,2]:
            for t in [3+2*k, 3+2*k+1]:
                ax.plot([positions[s][0], positions[t][0]],
                       [positions[s][1], positions[t][1]],
                       '-', color='#9B59B6', alpha=0.15, linewidth=1, zorder=1)
        # T-T edge
        ax.plot([positions[3+2*k][0], positions[3+2*k+1][0]],
               [positions[3+2*k][1], positions[3+2*k+1][1]],
               '-', color='#3498DB', alpha=0.2, linewidth=1, zorder=1)

    draw_vertices(ax, positions, vtypes, labels, size=250)

    # Simplex labels
    for k, lbl in enumerate(['A', 'B', 'C']):
        a = t_angles[k]
        ax.annotate(f'Simplex {lbl}', xy=(2.0*np.cos(a), 2.0*np.sin(a)),
                   fontsize=9, color='gray', ha='center', fontweight='bold', style='italic')

    ax.text(0, -4.2, '3 simplices × 10 hinges − shared SSS = 29 unique hinges',
            ha='center', fontsize=9, style='italic')


def diagram_beryllium(ax):
    """Beryllium: 4 simplices sharing SSS core."""
    ax.set_title('Beryllium (Be)\n4 simplices, shared SSS', fontsize=14, fontweight='bold')

    positions = {
        0: (0, 1.0),
        1: (-0.9, -0.3),
        2: (0.9, -0.3),
    }
    t_angles = [np.pi/4, 3*np.pi/4, 5*np.pi/4, 7*np.pi/4]
    r_inner, r_outer = 2.3, 3.0
    for k in range(4):
        a = t_angles[k]
        positions[3 + 2*k] = (r_inner * np.cos(a - 0.12), r_inner * np.sin(a - 0.12))
        positions[3 + 2*k + 1] = (r_outer * np.cos(a + 0.12), r_outer * np.sin(a + 0.12))

    vtypes = {0: 'S', 1: 'S', 2: 'S'}
    for k in range(8):
        vtypes[3+k] = 'T'

    labels = {0: 'S₁', 1: 'S₂', 2: 'S₃'}
    for k in range(8):
        labels[3+k] = f'T{k+1}'

    # SSS core
    draw_hinge_triangle(ax, positions[0], positions[1], positions[2], '#E74C3C', 0.3)

    for k in range(4):
        for s in [0,1,2]:
            for t in [3+2*k, 3+2*k+1]:
                ax.plot([positions[s][0], positions[t][0]],
                       [positions[s][1], positions[t][1]],
                       '-', color='#9B59B6', alpha=0.12, linewidth=1, zorder=1)
        ax.plot([positions[3+2*k][0], positions[3+2*k+1][0]],
               [positions[3+2*k][1], positions[3+2*k+1][1]],
               '-', color='#3498DB', alpha=0.15, linewidth=1, zorder=1)

    draw_vertices(ax, positions, vtypes, labels, size=200)

    for k, lbl in enumerate(['A', 'B', 'C', 'D']):
        a = t_angles[k]
        ax.annotate(f'{lbl}', xy=(1.8*np.cos(a), 1.8*np.sin(a)),
                   fontsize=10, color='gray', ha='center', fontweight='bold', style='italic')

    ax.text(0, -4.2, '4 simplices × 10 hinges − shared SSS = 39 unique hinges',
            ha='center', fontsize=9, style='italic')


# ═══════════════════════════════════════════════════════════════
#  Generate all diagrams
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    outdir = os.path.join(os.path.dirname(__file__), '..', '..', 'book', 'figures')
    os.makedirs(outdir, exist_ok=True)

    diagrams = [
        ('hydrogen', diagram_hydrogen),
        ('helium', diagram_helium),
        ('h2_molecule', diagram_h2_molecule),
        ('lithium', diagram_lithium),
        ('beryllium', diagram_beryllium),
    ]

    # Individual diagrams
    for name, func in diagrams:
        fig, ax = plt.subplots(1, 1, figsize=(8, 7))
        func(ax)
        ax.set_xlim(-5, 5)
        ax.set_ylim(-4.5, 4.5)
        ax.set_aspect('equal')
        ax.axis('off')

        # Legend
        from matplotlib.lines import Line2D
        legend_elements = [
            Line2D([0], [0], marker='o', color='w', markerfacecolor=C_S,
                   markersize=12, label='S vertex (C³, quark)'),
            Line2D([0], [0], marker='o', color='w', markerfacecolor=C_T,
                   markersize=12, label='T vertex (C², electron/slot)'),
            plt.Polygon([(0,0)], alpha=0.3, color='#E74C3C', label='SSS hinge (strong)'),
            Line2D([0], [0], color='#9B59B6', alpha=0.5, label='S-T edge (EM/weak)'),
        ]
        ax.legend(handles=legend_elements, loc='lower left', fontsize=8,
                 framealpha=0.8)

        fpath = os.path.join(outdir, f'simplex_{name}.png')
        fig.savefig(fpath, dpi=150, bbox_inches='tight', facecolor='white')
        plt.close(fig)
        print(f"Saved: {fpath}")

    # Combined overview
    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    for idx, (name, func) in enumerate(diagrams):
        row, col = divmod(idx, 3)
        ax = axes[row][col]
        func(ax)
        ax.set_xlim(-5, 5)
        ax.set_ylim(-4.5, 4.5)
        ax.set_aspect('equal')
        ax.axis('off')

    # Empty last cell → legend
    ax_legend = axes[1][2]
    ax_legend.axis('off')
    ax_legend.set_title('Legend', fontsize=14, fontweight='bold')
    ax_legend.text(0.5, 0.8, '● S vertex = C³ (quark/spatial)', transform=ax_legend.transAxes,
                  fontsize=12, color=C_S, ha='center', fontweight='bold')
    ax_legend.text(0.5, 0.65, '● T vertex = C² (electron/temporal)', transform=ax_legend.transAxes,
                  fontsize=12, color=C_T, ha='center', fontweight='bold')
    ax_legend.text(0.5, 0.50, '▲ SSS hinge = strong force (confined)', transform=ax_legend.transAxes,
                  fontsize=11, color='#E74C3C', ha='center')
    ax_legend.text(0.5, 0.38, '— S-T edge = EM/weak coupling', transform=ax_legend.transAxes,
                  fontsize=11, color='#9B59B6', ha='center')
    ax_legend.text(0.5, 0.26, '◆ Shared T = covalent bond', transform=ax_legend.transAxes,
                  fontsize=11, color=C_BOND, ha='center')
    ax_legend.text(0.5, 0.10, 'Each simplex = 5 vertices, 10 hinges\n'
                  'Atom = Z simplices sharing SSS core',
                  transform=ax_legend.transAxes, fontsize=10, ha='center', style='italic')

    fig.suptitle('DRLT Simplex Structures: Atoms and Molecules', fontsize=16, fontweight='bold', y=0.98)
    fig.tight_layout(rect=[0, 0, 1, 0.95])

    fpath = os.path.join(outdir, 'simplex_atoms_overview.png')
    fig.savefig(fpath, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close(fig)
    print(f"\nSaved overview: {fpath}")
    print("Done!")
