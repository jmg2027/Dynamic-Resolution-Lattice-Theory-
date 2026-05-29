#!/usr/bin/env python3
"""Raw branching-shape simulation (G-tower discussion, 2026-05-29).

Model: a point is an atom (a,b) or an UNORDERED pair {x,y} of two
DISTINCT points (slash_comm + x!=y).  S_0={a,b};
S_n = {a,b} U { {x,y} : x,y in S_{n-1}, x!=y }.
This is exactly the Raw recurrence |S_n| = 2 + C(|S_{n-1}|,2).
"""
from math import comb
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

A, B = "a", "b"

def gen(N):
    levels = [ {A, B} ]
    for _ in range(N):
        prev = levels[-1]
        nxt = {A, B}
        pl = list(prev)
        for i in range(len(pl)):
            for j in range(i+1, len(pl)):
                nxt.add(frozenset((pl[i], pl[j])))
        levels.append(nxt)
    return levels

import functools
@functools.lru_cache(maxsize=None)
def depth(p):
    if p in (A, B): return 0
    return 1 + max(depth(x) for x in p)
@functools.lru_cache(maxsize=None)
def pos(p):                       # 1D midpoint (dyadic) embedding
    if p == A: return 0.0
    if p == B: return 1.0
    xs = list(p); return (pos(xs[0]) + pos(xs[1])) / 2.0
@functools.lru_cache(maxsize=None)
def rep(p):
    if p in (A, B): return p
    xs = sorted(p, key=rep); return "(" + rep(xs[0]) + "/" + rep(xs[1]) + ")"

# ---- counts + completeness (intrinsic, via recurrence to n=12) ----
a = [2]
for _ in range(10): a.append(2 + comb(a[-1], 2))
comp = [ (a[n]-2)/comb(a[n],2) if a[n] >= 2 else 0 for n in range(len(a)) ]
print("level :", list(range(len(a))))
print("|S_n| :", a[:7], "...")
print("residue r_n = 1 - c_n :", [round(1-c,4) for c in comp[:9]])

# ---- objects up to level 5 ----
L = gen(5)
print("verify counts:", [len(s) for s in L])
for n,s in enumerate(L):
    dpos = len({round(pos(p),12) for p in s})
    print(f"  S_{n}: |S|={len(s):5d}  distinct 1D positions={dpos:5d}  "
          f"(Lens loses {len(s)-dpos})")

# ---- FAITHFULNESS: set-equal to Lean's explicit enumeration ----
# (RawDepth3.lean defines depthLe3List = depthLe2List ++ [t1..t7] with
#  s_ab=a/b, s_a_ab=a/(a/b), s_b_ab=b/(a/b); t1..t7 the 7 depth-3 pairs.)
def _fs(*xs): return frozenset(xs)
_s_ab = _fs(A, B); _saab = _fs(A, _s_ab); _sbab = _fs(B, _s_ab)
_lean_d2 = {A, B, _s_ab, _saab, _sbab}
_lean_d3 = _lean_d2 | {_fs(_saab, _sbab), _fs(A, _saab), _fs(B, _saab),
                       _fs(_s_ab, _saab), _fs(A, _sbab), _fs(B, _sbab),
                       _fs(_s_ab, _sbab)}
assert L[2] == _lean_d2, "S_2 != RawDepthCount.depthLe2List"
assert L[3] == _lean_d3, "S_3 != RawDepth3.depthLe3List"
print("FAITHFULNESS: S_2, S_3 SET-EQUAL to Lean depthLe{2,3}List "
      "(RawDepth3.lean, structure not count): PASS")

fig = plt.figure(figsize=(15, 11))

# Panel A: counts + completeness
axA = fig.add_subplot(2,2,1)
ns = list(range(len(a)))
axA.semilogy(ns, a, "o-", color="C0", label="|S_n|  (points)")
axA.semilogy(ns, [a[n]-2 for n in ns], "s--", color="C2",
             label="realized pairs (=|S_n|-2)")
axA.semilogy(ns, [comb(a[n],2) for n in ns], "^:", color="C3",
             label="all pairs C(|S_n|,2)")
axA.set_xlabel("level n"); axA.set_ylabel("count (log)")
axA.set_title("A.  points explode as a^2, realized pairs only as a\n"
              "=> completeness c_n -> 0  (void RECEDES)")
axA.legend(fontsize=8); axA.grid(True, alpha=.3)
axB2 = axA.twinx()
axB2.plot(ns, [1-c for c in comp], "d-", color="C1")
axB2.set_ylabel("residue ratio  r_n = 1 - c_n", color="C1")
axB2.set_ylim(0,1.05); axB2.tick_params(axis='y', labelcolor="C1")

# Panel B: 1D dyadic embedding
axB = fig.add_subplot(2,2,2)
for n in range(6):
    P = sorted({pos(p) for p in L[n]})
    axB.scatter(P, [n]*len(P), s=14, color="C0")
axB.scatter([0.375],[3], s=120, facecolors="none", edgecolors="red", linewidths=2)
axB.annotate("3/8: TWO distinct Raw points\n(ab)/(a/ab) and a/(b/ab)\ncollapse here "
             "(1D Lens is non-injective:\nit erases part of the residue)",
             (0.375,3), (0.40,4.1), fontsize=8, color="red",
             arrowprops=dict(arrowstyle="->", color="red"))
axB.set_xlabel("midpoint (dyadic) position in [0,1]"); axB.set_ylabel("level n")
axB.set_title("B.  midpoint-Lens: Raw -> dyadic residue of [0,1]\n"
              "void = full continuum (unreached); Raw = dense gaps")
axB.grid(True, alpha=.3)

# Panel C: constituent DAG up to level 3 (self-nesting)
axC = fig.add_subplot(2,2,3)
S3 = L[3]
bylayer = {}
for p in S3: bylayer.setdefault(depth(p), []).append(p)
xy = {}
for d in sorted(bylayer):
    row = sorted(bylayer[d], key=rep); k = len(row)
    for i,p in enumerate(row):
        xy[p] = ((i+1)/(k+1), d)
for p in S3:
    if p not in (A,B):
        for c in p:
            axC.plot([xy[p][0],xy[c][0]],[xy[p][1],xy[c][1]],
                     color="gray", alpha=.5, lw=.8, zorder=1)
for p in S3:
    x,y = xy[p]
    atom = p in (A,B)
    axC.scatter([x],[y], s=420 if atom else 230,
                color="C3" if atom else "C0", zorder=2)
    axC.annotate(rep(p), (x,y), fontsize=6.5, ha="center", va="center",
                 color="white" if atom else "black", zorder=3)
axC.set_ylabel("depth"); axC.set_xticks([])
axC.set_title("C.  constituent DAG (S_3, 12 pts): each point -> its 2 parts\n"
              "a,b (red) REUSED at every depth = self-nesting (not new space)")
axC.invert_yaxis(); axC.grid(True, axis="y", alpha=.3)

# Panel D: 3-seed triangle subdivision (your intuition) + asymmetry note
axD = fig.add_subplot(2,2,4)
import numpy as np
tri = {0:np.array([0,0.0]),1:np.array([1,0.0]),2:np.array([0.5,0.866])}
def subdivide(pts):
    new = dict(pts); idx = max(pts)+1; keys=list(pts)
    seen=set()
    for i in range(len(keys)):
        for j in range(i+1,len(keys)):
            m = tuple(np.round((pts[keys[i]]+pts[keys[j]])/2,6))
            if m in seen: continue
            seen.add(m); new[idx]=np.array(m); idx+=1
    return new
pts = dict(tri)
hist=[dict(pts)]
for _ in range(3):
    pts = subdivide(pts); hist.append(dict(pts))
cols=["C3","C0","C2","C1"]
for k,h in enumerate(hist):
    P=np.array(list(h.values()))
    axD.scatter(P[:,0],P[:,1], s=max(60-15*k,8), color=cols[k],
                label=f"iter {k}: {len(h)} pts")
axD.set_title("D.  3-SEED toy (full triangle, all 3 midpoints):\n"
              "-> Sierpinski.  But real Raw has 2 seeds; the 1st pair ab\n"
              "doubles as a vertex => one edge is NOT re-drawn => ASYMMETRIC\n"
              "(why 'beyond level 2 is tricky' -- it's not clean Sierpinski)")
axD.legend(fontsize=7); axD.set_aspect("equal"); axD.grid(True, alpha=.3)

fig.suptitle("The shape of Raw branching  (S_n = {a,b} U pairs(S_{n-1}); "
             "|S_n| = 2 + C(|S_{n-1}|,2) = 2,3,5,12,68,2280,...)",
             fontsize=13, y=0.995)
fig.tight_layout(rect=[0,0,1,0.97])
out = "research-notes/data/probes/raw_branching_shape.png"
fig.savefig(out, dpi=110)
print("saved", out)
