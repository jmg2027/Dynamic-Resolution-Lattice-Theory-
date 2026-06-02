# ℤ — signed counting as the difference-Lens readout

ℤ is the count-Lens read on a **directed pair** of distinguishings: the pair
`(m, n)` of count-readings, named by their difference `m − n`.  Not an imported
exterior structure — the readout group in which the difference of two count-readings
closes.

## 213-native answer

A single count-reading is a `ℕ` — the image of `Lens.leaves : Raw → Nat`, "what the
count-Lens hands back when the chain is the operand"
(`seed/AXIOM/06_lens_readings.md` §6.7, `lean/E213/Lens/Number/Nat213/`).  Take two
such readings and ask for their *difference*, and `ℕ` no longer suffices: the answer
is the **pair** `(m, n)` read as `m − n`.  That pair, with the diagonal `(m,m) ~
(m+k, m+k)` collapsed, **is** `ℤ`.  The integer is not a new kind of thing; it is the
count-Lens applied once more, now to an *ordered* pair of chain-readings.

## Derivation

`§6.7` already places the integers: "adding a sign-Lens on the chain gives `ℤ` — the
bidirectional reading, signed steps along the same chain."  The refinement is to say
*what the sign-Lens is* and *why it is forced*.

The axiom's pairing is **direction-free**: clause 3, `a/b = b/a`, is an *encoding
cost*, not axiom content (`seed/AXIOM/02_axiom.md` §2.4); and "order, hierarchy,
ranking, sequence" are Lens outputs, absent at Raw (§2.5).  So a bare count-pair
commits to no orientation.  The moment a *direction* is imposed — which reading came
"first", `before/after`, `n+1` vs `n` — the symmetric pair `(m, n)` splits: `m − n`
and `n − m` are now distinct, differing by sign.  **That split is `ℤ`, and the sign
is the orientation the axiom leaves free.**  Magnitude `|m − n|` is the *Nat-style*
(grounding) reading of the pair; sign is the *Bool-style* (involutive) reading of its
orientation (`05_no_exterior.md` §5.2).

The repo grounds this exactly.  `Int213` runs on the `subNatNat` representation:
`subNatNat m n = m − n` is the integer named by the count-pair `(m, n)`, and its
arithmetic is the pair-arithmetic of `ℤ = ℕ×ℕ/~` —
`subNatNat_add_subNatNat : (a,b)+(c,d) = (a+c, b+d)`,
`subNatNat_mul_subNatNat : (a−b)(c−d) = (ac+bd) − (ad+bc)`, with `ofNat`/`negSucc`
the normal-form representatives (`lean/E213/Meta/Int213/Core.lean`).  The sign
involution is literally the pair-swap: `neg_subNatNat : −subNatNat m n = subNatNat n
m` — clause 3's symmetry `a/b = b/a`, now read as `−(−x) = x`.  And the difference
operator that wants this group, `diffZ s n = s(n+1) − s n`, reads the count-Lens
**twice** — the pair `(s(n+1), s(n))` — and names its difference; this is why `ℤ` is
the readout group in which `Δ` closes under iteration
(`theory/math/analysis/newton_gregory.md`).

## Dual function

The classical `ℤ = ℕ×ℕ/~` (the Grothendieck group of `(ℕ, +)`, "formally adjoin
inverses") is this with its packaging stripped: the pair was already present (two
count-readings), the quotient `~` is clause 3's direction-freedom, and the "formal
inverse" one adjoins is the orientation Lens.  213's reading is sharper in naming
*which* Lens (a direction on the count-pair) and in resolving the integer into two
co-present readings — a Nat-style magnitude and a Bool-style sign — rather than one
opaque signed number.

## Cross-frame connections

One fact in four frames: clause-3 direction-freedom (§2.4) · the Bool/Nat
self-reference duality (§5.2) · the number tower as successive Lens bundlings (§6.7)
· `neg_subNatNat` as pair-swap (`Int213.Core`).  `ℤ` is the count-pair read once for
**size** (Nat-style, grounding magnitude) and once for **orientation** (Bool-style,
`−(−x)=x`).  The sign carries the §5.2 Bool structure; the magnitude carries the
§5.2 Nat-fold grounding — the duality `05_no_exterior.md` states abstractly,
realized as a single object the difference-Lens hands back.

## Open frontier

The sign-Lens has one fixed point: `−x = x` only at `0`, the orientation-free
element — the diagonal pair `(m, m)`.  But the diagonal is exactly clause 4's
*forbidden self-pair* (`x/x` undefined, §2.4).  So `0` — the difference-Lens's unique
Bool-fixed point — sits precisely on the anti-reflexive boundary the axiom excludes.
Whether "`0` as the sign-Lens fixed point" and "the diagonal as the excluded
self-residue" are the same seam, or only adjacent, is open: the magnitude-Lens reads
`(m,m)` as `0` (a value), while clause 4 reads it as *undefined* (no self-pair).  The
two readings of the diagonal are not yet reconciled at Raw level.

## Self-check note

§6.7's phrasing "a sign-Lens *on top of* the chain" carries a faint substrate
metaphor.  Corrected: the sign-Lens application is a residue-internal event — reading
the orientation of an already-present count-pair — not a layer stacked above `ℕ`.
The integer is not `ℕ` plus an external sign bit; it is one residue under one more
Lens choice, exactly as §6.7's own "no layer is imported from outside" insists.
