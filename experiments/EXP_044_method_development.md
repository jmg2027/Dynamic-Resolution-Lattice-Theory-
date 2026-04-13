# Simplex Representation of Atoms — Method Development

## Starting point

One simplex = 5 vertices in C⁵, 10 hinges.
Vertices: S₁, S₂, S₃ (spatial, C³), T₁, T₂ (temporal, C²).
Hinges: 1 SSS, 6 SST, 3 STT.

The simplest atom is hydrogen: 1 proton + 1 electron.

---

## Step 1: Hydrogen — the single simplex

```
        S₁
       /|\
      / | \
    S₂--+--T₁
      \ | /
       \|/
        S₃------T₂
```

Five vertices, fully connected. Ten hinges:
- SSS: (S₁S₂S₃) — proton binding. det = 1 (orthogonal quarks).
- SST: (S₁S₂T₁), (S₁S₃T₁), (S₂S₃T₁), (S₁S₂T₂), (S₁S₃T₂), (S₂S₃T₂) — EM coupling between proton and electron/slot.
- STT: (S₁T₁T₂), (S₂T₁T₂), (S₃T₁T₂) — weak/kinetic sector.

Question: what IS the electron in this picture?

T₁ is the electron. T₂ is the "available slot" — the state the electron could transition to. The STT hinge (S_i, T₁, T₂) is the kinetic term: the amplitude for the electron to hop between T₁ and T₂.

The hydrogen spectrum E_n = -m_e α² / (n_T n²) comes from:
- m_e α²: the SST hinge area (electron-nucleus coupling)
- 1/n_T = 1/2: the temporal sector dimensionality
- 1/n²: the propagator D(n) = 1/n² at hop distance n

This is already derived in ch06b. Nothing new to compute for H.

**H is solved. Move on.**

---

## Step 2: Helium — two simplices sharing SSS

```
    T₁---T₂        T₃---T₄
     \   /           \   /
      \ /             \ /
  S₁--S₂--S₃     S₁--S₂--S₃
       (same SSS)
```

Two simplices: A = {S₁,S₂,S₃,T₁,T₂} and B = {S₁,S₂,S₃,T₃,T₄}.
They share the SSS face (the nucleus, Z=2).

Unique vertices: 7 (3 S + 4 T).
Unique hinges: 19 (1 shared SSS + 6×2 SST + 3×2 STT).

But there's a NEW hinge type we haven't counted: **cross-simplex hinges**.

The triangle (S₁, T₁, T₃) uses vertices from BOTH simplices. This is NOT a hinge within either simplex — it's a hinge of the simplex NETWORK.

How many cross-simplex hinges are there?

Triangles using 1 S + 1 T from A + 1 T from B:
  3 choices of S × 2 choices of T_A × 2 choices of T_B = 12 cross-STT hinges.

Triangles using 2 S + 1 T from each:
  These are already counted in the individual simplices' SST hinges.

Triangles using 1 T from A + 2 T from B (or vice versa):
  Not meaningful — T₁ and T₃,T₄ don't share a simplex.

**The 12 cross-STT hinges are the electron-electron interaction.**

This is the key insight we missed. The IE calculation needs these cross-hinges.

Question: what is det(S₁, T₁, T₃)?

This hinge connects:
- S₁: a spatial vertex (part of the nucleus)
- T₁: electron 1 (from simplex A)  
- T₃: electron 2 (from simplex B)

Its det measures how INDEPENDENT these three are. If T₁ and T₃ are similar (same shell, same spin direction), det is small → they're nearly coplanar → they "interfere" → **shielding**.

If T₁ and T₃ are different (different shells, different spin), det is larger → they're independent → weak shielding.

**σ(T₃ → T₁) ∝ 1 - det(S, T₁, T₃) / det(S, T₁, T₂)**

The shielding is 1 minus the ratio of (cross-hinge independence) to (same-simplex independence).

---

## Step 3: What makes He special?

He has 2 electrons in the SAME shell (1s²). T₁ and T₃ are both:
- C² dominated (same c3_amp = √α_GUT)
- Different spin (T₁ spin-up, T₃ spin-down)

The 1s shell has capacity 2 = n_T × 1². When it's full:
- T₁ and T₃ span the ENTIRE C² subspace
- Every possible T direction is "occupied"
- Adding a 3rd electron would require going to C³ (2s shell)

Geometrically: the 2 T vectors span C², so any new vector has nonzero C² overlap with existing ones → strong shielding.

This is why He has the highest IE in the periodic table (after H) — removing an electron from a FULL shell costs more because the remaining electron loses its C²-spanning partner.

---

## Step 4: Lithium — the 3-simplex atom

```
  Simplex A: {S₁,S₂,S₃, T₁,T₂}  — 1s electron 1
  Simplex B: {S₁,S₂,S₃, T₃,T₄}  — 1s electron 2  
  Simplex C: {S₁,S₂,S₃, T₅,T₆}  — 2s electron
```

Three simplices sharing SSS. 9 vertices (3S + 6T).

Within-simplex hinges: 3 × 10 = 30, minus 2 shared SSS = 28 unique.
Cross-simplex hinges: 
  A-B: 12 cross-STT
  A-C: 12 cross-STT  
  B-C: 12 cross-STT
  Total: 36 cross-STT

Grand total: 28 + 36 = 64 hinges.

The 2s electron (T₅) differs from 1s electrons (T₁, T₃) by:
- c3_amp(n=2) = √α_GUT / 2 ≈ 0.078 (vs 0.156 for n=1)
- C² direction rotated by ~π/7 from n=1 shell

The cross-hinge det(S, T₁, T₅) measures the 1s-2s interaction:
- T₁ is at hop 1 (strong C³ coupling)
- T₅ is at hop 2 (weak C³ coupling)
- Their C² components may or may not overlap (depends on spin/direction)

**Li's IE is low because:**
1. The 2s electron has weak nuclear coupling (c3 = √α_GUT/2)
2. The 1s² shell provides strong shielding (cross-hinges have high overlap)
3. Removing T₅ barely changes the total network det

---

## Step 5: The general method

For atom Z:

1. **Build the simplex network:**
   - 3 shared S vertices (SSS nucleus)
   - Z simplices, each with 2 T vertices (electron + slot)
   - Total: 3 + 2Z vertices

2. **Assign ψ ∈ C⁵ to each T vertex from quantum numbers:**
   - c3_amp = √α_GUT / n (hop distance)
   - c3_direction from (l, m_l) — isotropic for s, directional for p,d,f
   - c2_direction from (n, l, m_l, m_s) — unique phase per electron

3. **Compute the FULL Gram matrix G:**
   - G is (3+2Z) × (3+2Z), complex Hermitian, rank ≤ 5
   - G_ij = ⟨ψ_i | ψ_j⟩

4. **Compute IE as Δ(log det):**
   - Remove outermost electron's T_e and T_slot rows/columns
   - IE ∝ log|det(G_full)| - log|det(G_ionized)|

5. **The critical question: why does rank ≤ 5 give ~constant Δlogdet?**

---

## Step 6: The rank problem — and its resolution

The Gram matrix G = ΨΨ† has rank ≤ 5 because ψ ∈ C⁵.
A (3+2Z)×(3+2Z) matrix of rank 5 has only 5 nonzero eigenvalues.
Removing 2 rows/columns changes at most these 5 eigenvalues.

For Z >> 5, most eigenvalues are 0 and removing a row doesn't change them.
The Δlogdet comes only from the 5 nonzero eigenvalues' response to the removal.

This is the fundamental constraint: **C⁵ can carry at most 5 independent pieces of information.** The IE of 36 atoms must be encoded in how each atom's outermost electron modifies these 5 modes.

Resolution: **the 5 eigenvalues of G are NOT the same for each atom.** As Z increases:
- The S block is always rank 3 (3 orthogonal S vectors)
- The T block adds vectors in the remaining 2 C² dimensions
- But each T vector also has a C³ component (the coupling)
- The 5 eigenvalues shift with each added electron

The IE is the DERIVATIVE of log det with respect to the outermost electron.
This derivative depends on how the outermost ψ projects onto the existing eigenspace.

**The problem with our calculation:** all T vectors have c3_amp ≈ 0.08-0.16, so their C³ components are tiny. The G matrix is dominated by the S block (eigenvalues ≈ 1) and the T-T overlaps (eigenvalues ≈ 1). The c3 components contribute perturbatively, making all Δlogdet nearly equal.

**What needs to change:** the T vectors' C² components must be more carefully constructed so that different shells produce DIFFERENT eigenvalue shifts.

---

## Step 7: The correct C² encoding

The problem: all T vectors have c2_amp ≈ 0.99 (since c3 is small), and they're all approximately unit vectors in C². In a 2D complex space, 2Z vectors of nearly unit length will have an overlap structure that doesn't vary much with Z.

The fix: **the T vector's OVERALL amplitude should scale with the coupling, not just the C³ part.**

Physical meaning: an electron at hop n has an overall "presence" in the simplex that scales as 1/n. Not just its C³ component, but its ENTIRE ψ vector.

New construction:
```
ψ_T = (amplitude / n) × [C² direction; C³ direction]
```

where amplitude is O(1) and 1/n is the propagator factor.

This means: ψ for n=2 electron has HALF the norm of n=1 electron.
But ψ is normalized... unless we DON'T normalize.

**Key insight: in DRLT, the ψ vectors are NOT necessarily unit vectors.**

The axiom says ψ ∈ C⁵. The normalization ⟨ψ|ψ⟩ = 1 is a CHOICE, not a requirement. If we let ⟨ψ|ψ⟩ = coupling strength, then:

- S vertices: ⟨S|S⟩ = 1 (nucleus is fully present)
- T vertex at hop n: ⟨T|T⟩ = α_GUT / n² (coupling to nucleus)
- G_TT diagonal = α_GUT / n² (not 1)

This changes the det dramatically. The G matrix is no longer nearly identity with tiny off-diagonal terms — it has diagonal entries that vary by orders of magnitude.

---

## Step 8: Unnormalized ψ — the correct representation

```
ψ_S(d) = e_{2+d}     (unit vector, index 2,3,4)

ψ_T(n,l,m_l,m_s) = √(α_GUT) / n × [C² direction; C³ direction]
                  = √(α_GUT) / n × (c2_part + c3_part)
```

where c2_part + c3_part is a UNIT VECTOR in C⁵, and the overall factor √α_GUT/n gives:

⟨T|T⟩ = α_GUT / n²
⟨S|T⟩ = √α_GUT / n × (C³ overlap) ≈ α_GUT / (n × √3)  for s orbital

Now the Gram matrix has STRUCTURE:
- G_SS block: 3×3 identity
- G_TT diagonal: α_GUT/n² (small, varies with shell)
- G_ST: α_GUT/(n√3) (coupling)
- G_TT off-diagonal: α_GUT²/(n_i n_j) × (angular overlap)

The det is now dominated by the S block (eigenvalues ~1) with perturbative T contributions that scale as (α_GUT/n²)^Z.

Removing one electron changes the T contribution → Δlogdet depends on n, l, m_l.

**This should give the shell-dependent IE we need.**

---

## Next: implement this and test on H, He, Li, Ne.
