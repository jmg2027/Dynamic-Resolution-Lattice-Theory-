# Gauss's lemma — CLOSED (strict ∅-axiom)

**2026-06-05: Gauss's lemma is closed** — `GaussLemma.gauss_qr` (QR(a) ⟺ ∏signs=1) + `gauss_core`
(↑aᵐ ≡ ∏signs), 15 PURE + `ProdCongr` 3 PURE.  The plan below was executed in full.
Downstream now open: the **quadratic character of 2** (second supplement, p≡±1 mod 8) and
**quadratic reciprocity**.

---

# (original) Layer 3 plan

**Status (2026-06-05).**  Layers 1–2 closed strict ∅-axiom and committed:

- **Layer 1** `lean/E213/Lib/Math/Algebra/Linalg213/ProdCongr.lean` (3 PURE): `prodZ_congr_map`
  (elementwise `P ∣ (g x − h x) ⟹ P ∣ (∏g − ∏h)`), `prodZ_map_mul`, `prodZ_map_const_mul`.
- **Layer 2** `lean/E213/Lib/Math/NumberTheory/ModArith/GaussLemma.lean` (12 PURE): the half-system
  `seg m = [1..m]` (length/mem/Nodup), the `cntNodup_of_listNodup` bridge, the pigeonhole
  `mem_of_card_le`, the fold `fold a p m x = if (a·x mod p) ≤ m then (a·x mod p) else p − (a·x mod p)`,
  `fold_mem` (lands in `[1,m]`), `fold_inj` (injective on `seg m`), and ★ `fold_perm`:
  `LPerm ((seg m).map (fold a p m)) (seg m)`.

The hard combinatorial core (the fold permutation) is **done**.

## Layer 3 — the product/congruence assembly (remaining)

Over `ℤ`, mapping `x ∈ seg m`, define list functions:
- `gZ x = ↑((a·x) % p)`, `axZ x = ↑a · ↑x`, `fZ x = ↑(fold a p m x)`,
  `sgZ x = if (a·x)%p ≤ m then (1:ℤ) else −1`, `sfZ x = sgZ x · fZ x`.

Products `P_• = prodZ ((seg m).map •)`; `M = prodZ ((seg m).map (fun x => (↑x:ℤ)))` (= `m!`).

Steps:
1. **`gZ ≡ axZ` mod p** elementwise (`↑((a·x)%p) ≡ ↑(a·x)`; helper `int_dvd_cast_sub_mod p n :
   p ∣ (↑n − ↑(n%p))` via `div_add_mod` + `natCast_sub`/`natCast_mul`) → `prodZ_congr_map` →
   `p ∣ (P_g − P_ax)`.
2. **`gZ ≡ sfZ` mod p** elementwise: low branch (`r ≤ m`) `gZ = sfZ = ↑r` (diff 0); high branch
   (`r > m`) `sfZ = −↑(p−r) = ↑r − ↑p`, diff `= ↑p` → `prodZ_congr_map` → `p ∣ (P_g − P_sf)`.
3. ⟹ `p ∣ (P_ax − P_sf)`.
4. **`P_ax = ↑a^m · M`** (`prodZ_map_const_mul`, len `= m` via `seg_length`).
5. **`P_sf = P_sg · P_f`** (`prodZ_map_mul`).
6. **`P_f = M`**: `(seg m).map fZ = ((seg m).map (fold a p m)).map (↑·)` (`List.map_map`); `fold_perm`
   + `map_lperm (↑·)` + `prodZ_lperm` ⟹ `prodZ = prodZ ((seg m).map ↑·) = M`.
7. ⟹ `p ∣ (↑a^m · M − P_sg · M) = M · (↑a^m − P_sg)`.  `M` is coprime to `p` (helper
   `not_dvd_prodZ`: prime `∤` product of units, induction + `int_euclid`; each `↑x`, `x ∈ [1,m]`,
   `p ∤ ↑x`), so `int_euclid` cancels: **`p ∣ (↑a^m − P_sg)`** = `gauss_core`.
8. **`P_sg ∈ {1, −1}`** (`prodZ` of `±1`s, induction).
9. **`gauss_qr`**: with Euler (`qr_iff_pow_one` / `euler_criterion`: `QR(a) ⟺ ↑a^m ≡ 1`) and `p ∤ 2`
   (so `1 ≢ −1`): `(∃ z, z² ≡ a) ⟺ P_sg = 1`.  This is Gauss's lemma in usable form (`P_sg` = the
   least-residue sign product = `(−1)^μ`).
10. (optional) define `μ = ((seg m).filter (m < (a·x)%p)).length` and prove `P_sg = (−1)^μ`.

### Helpers needed (new)
`int_dvd_cast_sub_mod`, `not_dvd_prodZ` (prime ∤ product of units), `prodZ_pm_of_pm` (∏ of ±1 is
±1), the `map_map`/`map_lperm` glue for step 6.  Casts: `natCast_sub` (EulerConverse), `natCast_mul`/
`natCast_pow` (NonFixedExists), `int_euclid`/`int_dvd_to_nat` (PolyRoot).

## Downstream once Gauss lands
Quadratic character of `2` (second supplement, `2` QR ⟺ `p ≡ ±1 mod 8`); quadratic reciprocity.

## Cross-references
`lean/E213/Lib/Math/Algebra/Linalg213/{ProdLperm,ProdCongr}.lean`,
`…/ModArith/GaussLemma.lean`, `…/ModArith/LegendreMultiplicative.lean` (`qr_iff_pow_one`),
`…/PolyRoot/IntEuclid.lean` (`int_euclid`).
