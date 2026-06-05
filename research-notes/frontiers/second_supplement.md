# Quadratic character of 2 (second supplement) — reduced to a finite count

**Status (2026-06-05).**  Reduced strict ∅-axiom to an `m`-only computation
(`lean/E213/Lib/Math/NumberTheory/ModArith/SecondSupplement.lean`, 3 PURE):

- `two_qr_iff`: `2` is a QR mod `p` ⟺ `∏ₓ∈[1,m] (if 2x ≤ m then 1 else −1) = 1`.  (No wraparound:
  `2x ≤ 2m = p−1 < p`, so `sgFn 2 = (if 2x ≤ m …)`; then `gauss_qr`.)
- `prodZ_sign_eq`: a `±1`-product `= (−1)^(countNeg)` (`countNeg` = #`−1`s).

So `2` QR ⟺ `(−1)^μ = 1` ⟺ `μ` even, where `μ = countNeg ((seg m).map (fun x => if 2x ≤ m …))
= #{x ∈ [1,m] : 2x > m}`.

## Remaining (a self-contained finite count + mod arithmetic)

The threshold `m` is **coupled to the list length `m`**, so a direct induction on `seg m` does not
telescope (incrementing `m` re-signs every old element).  Decouple with a fixed-threshold counter `k`:

1. `signProd m k := ∏_{x=1}^{k} (if 2x ≤ m then 1 else −1)` (recursion on `k`, `m` fixed) and
   `prodZ ((seg m).map (fun x => if 2x ≤ m …)) = signProd m m` (seg is `[1..m]` in order).
2. `cnt2 m k := #{x ∈ [1,k] : 2x > m}` (recursion on `k`); `signProd m k = (−1)^(cnt2 m k)` (induction
   on `k`, using `prodZ_sign_eq`-style step).
3. `cnt2 m m = m − m/2`  (= `m − #{x ≤ m/2}`; `#{x ∈ [1,m] : 2x ≤ m} = m/2` since `m/2 ≤ m`).
4. **Parity bridge**: `(m − m/2) % 2 = 0  ⟺  m % 4 = 0 ∨ m % 4 = 3`  (case on `m % 4`, `m = 4q+r`,
   `decide` on `r`).
5. **`m % 4 ↔ p % 8`** (`p = 2m+1`):  `m%4 ∈ {0,3} ⟺ p%8 ∈ {1,7}` (mirror `even_iff_pmod4`'s
   `add_mul_mod_self_pure` computation).
6. ★ `second_supplement`: `(∃ z, z² ≡ 2 mod p) ⟺ p % 8 = 1 ∨ p % 8 = 7`.

Estimated ~100 lines; all elementary (no new infrastructure — `prodZ_sign_eq` + `add_mul_mod_self_pure`
+ `decide` on residues).  Watch the usual propext-dirty core lemmas (`Nat.mod_self`,
`Nat.sub_eq_of_eq_add`, `Int.mul_one`, term-mode `if`) — use the pure repo replacements.

## Downstream
Quadratic reciprocity (Eisenstein lattice-point count, or the Gauss-lemma `μ`-sum).

## Cross-references
`lean/E213/Lib/Math/NumberTheory/ModArith/{SecondSupplement,GaussLemma}.lean`,
`…/EulerFirstSupplement.lean` (`even_iff_pmod4`, the `m`-parity ↔ `p`-mod template).
