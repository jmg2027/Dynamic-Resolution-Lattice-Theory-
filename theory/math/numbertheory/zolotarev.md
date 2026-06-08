# Zolotarev's lemma — the Legendre symbol is a permutation sign

The Legendre symbol `(a/p)` — proven in `legendre_symbol.md` as a count-Lens
parity bit — has a second face: it is the **sign of a permutation**.  For an odd
prime `p` and a unit `a`, multiplication-by-`a` permutes the residues
`{0,1,…,p−1}`; **Zolotarev's lemma** says the sign of that permutation *is* the
Legendre symbol:

```
psign (σ_a)  =  (a/p),      σ_a : x ↦ a·x mod p.
```

This chapter records the full result — closed ∅-axiom for **every** odd prime —
and how it falls out of the determinant/permutation-sign machinery
(`Linalg213`) meeting the Gauss-`μ` count (`GaussLemma`).  It is the missing
edge of the **"one permutation, three readouts"** square: the inversion sign,
the determinant of the permutation matrix, and the Legendre symbol are one
object.

## 213-native answer

There is no "sign primitive" any more than a Legendre primitive.  A permutation
is carried as its **value-list** `[σ 0, σ 1, …]`; its sign is the count-Lens
parity of the inversion count, `psign σ := altSign (inversions σ)`
(`Linalg213.Permutation`).  `σ_a` is the value-list
`mulPermMod a p = (iota p).map (·*a % p)`.  So both sides of Zolotarev are
parity bits of explicit counts:

- `(a/p) = 1` is `∏_{x∈[1,m]} sgFn(a·x) = 1`, the half-system sign-product
  (`gauss_qr`), `m = (p−1)/2`;
- `psign σ_a = 1` is `inversions (mulPermMod a p)` even.

Zolotarev is the statement that these two counts have the **same parity** — no
external "symbol", no character theory assumed.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/NumberTheory/ModArith/Zolotarev*.lean`
  (the count-Lens / number-theory deployment) on top of
  `lean/E213/Lib/Math/Algebra/Linalg213/InversionsAppend.lean` (the reusable
  permutation-sign combinatorics).
- **∅-axiom status**: **44 PURE / 0 DIRTY** (7 + 23 + 14 number-theory) plus the
  28 PURE `InversionsAppend` infra it rests on.

| file | content | PURE |
|---|---|---|
| `ZolotarevSign.lean` | `mulPermMod` (the value-list of `σ_a`), `mulPermMod_mem_perms`, `mulPermMod_comp` (`σ_a∘σ_b=σ_{ab}`), `psign_mulPermMod` (sign homomorphism), `psign_mulPermMod_qr` (**QR ⟹ even**, the residue side) | 7 |
| `ZolotarevConverse.lean` | `psign_mulPermMod_negone = (−1)^m` (reversal sign), `psign_mulPermMod_negone_qr` (`= (−1/p)`, the `−1` corner), `zolotarev_pmod4_three` (full identity for `p ≡ 3 mod 4`), `det_permMatrix_mulPermMod_pmod4_three` | 23 |
| `ZolotarevMuBridge.lean` | `mulPermMod_block` (`σ_a` is `0::(fh ++ (revL fh).map(p−·))`), `psign_mulPermMod_eq_diag`, `altSign_diag_eq_prodSgn`, ★ `zolotarev_mu`, `det_permMatrix_mulPermMod` | 14 |
| `Linalg213/InversionsAppend.lean` | `inversions_append`, `psign_append`, `psign_csub_revL`, `psign_blockForm`, `altSign_crossInv_map_psub` (symmetric-cross-count parity), `getD`/`revL` plumbing | 28 |

## Key results

| Theorem | Lean | Statement (informal) |
|---|---|---|
| `psign_mulPermMod` | `ZolotarevSign` | `a ↦ psign σ_a` is a homomorphism `(ℤ/p)^× → {±1}` |
| `psign_mulPermMod_qr` | `ZolotarevSign` | **residue side**: `QR(a) ⟹ psign σ_a = 1` (`σ_a = σ_z∘σ_z`) |
| `psign_mulPermMod_negone` | `ZolotarevConverse` | `psign σ_{−1} = (−1)^m` (the reversal has `tri₂(p−1)` inversions, parity `m`) |
| `zolotarev_pmod4_three` | `ZolotarevConverse` | `psign σ_a = (a/p)` for `p ≡ 3 (mod 4)` (`−1` is the nontriviality witness) |
| ★ `zolotarev_mu` | `ZolotarevMuBridge` | **Zolotarev (full)**: `psign σ_a = 1 ⟺ QR(a)`, every odd prime |
| `det_permMatrix_mulPermMod` | `ZolotarevMuBridge` | `det (permMatrix σ_a) = (a/p)` — the three readouts coincide |

## Narrative

**The residue side** is immediate from the homomorphism: a quadratic residue
`a ≡ z²` gives `σ_a = σ_z ∘ σ_z`, a square, so `psign σ_a = (psign σ_z)² = 1`
(`psign_mulPermMod_qr`).  Via `gauss_qr` this already matches `(a/p)` on the
residue subgroup.

**The converse** — non-residue ⟹ odd permutation, i.e. the character is
*nontrivial* — is the content.  The decisive structural fact is that `σ_a`
commutes with negation: `σ_a(p−x) = p − σ_a(x)`.  As a value-list this means
`σ_a` is automatically in **block form**

```
mulPermMod a p  =  0 :: (fh ++ (revL fh).map (p−·)),      fh = [σ_a 1, …, σ_a m]
```

(`mulPermMod_block`).  The general block-form sign lemma `psign_blockForm`
(`InversionsAppend`) collapses such a list's sign to a single **cross-inversion
count** — the leading `0` contributes nothing, and the two halves carry equal
sign (value-negation `p−·` and reversal each flip every pairwise comparison, so
composed they cancel: `psign_csub_revL`).  Thus

```
psign σ_a  =  altSign (crossInv fh (fh.map (p−·))).
```

This cross count `= #{(x,w)∈fh² : x+w>p}` is **symmetric** in `(x,w)`
(`psub_lt_symm`: `p−w<x ↔ p−x<w`), so its off-diagonal pairs come in twos and
cancel mod 2; only the diagonal `#{x∈fh : 2x>p} = #{x∈fh : x>m}` survives
(`altSign_crossInv_map_psub`).  That diagonal is exactly Gauss's `μ` — the count
of half-system multiples that exceed `m` — so `psign σ_a = (−1)^μ = ∏ sgFn`
(`altSign_diag_eq_prodSgn`).  Composing with Gauss's lemma `gauss_qr`
(`∏ sgFn = 1 ⟺ QR`) gives `psign σ_a = 1 ⟺ QR(a)`: Zolotarev, for every odd
prime (`zolotarev_mu`).

**No primitive root** is needed.  The classical proof routes through a generator
`g` (then `σ_g` is a single `(p−1)`-cycle of sign `−1`); the symmetric-cross-count
parity replaces that with a direct combinatorial identity, which is why the whole
converse is `∅`-axiom without any cyclicity-of-units infrastructure.

**Three readouts as one.**  `det_permMatrix : det (permMatrix σ) = psign σ`
(`Linalg213.PermMatrixDet`) makes the Legendre symbol literally the determinant of
the permutation matrix of `×a mod p` (`det_permMatrix_mulPermMod`): the inversion
sign, the determinant, and `(a/p)` are three readings of one permutation.

## Open frontier

None for Zolotarev itself (closed, all odd primes).  The neighbouring open
synthesis directions — the Teichmüller `ω`-projection face of the quadratic
character, the `ZpSeq ↠ ℤ/pⁿ ↠ ℤ/p` truncation tower, and the Hensel/`diagLimit`
square-root face — are tracked in
`research-notes/frontiers/` (the "permutation's three readouts" board, insights
2–4).

## How to verify

```bash
cd lean && lake build E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge
python3 ../tools/scan_axioms.py E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge   # 14 PURE / 0 DIRTY
```
