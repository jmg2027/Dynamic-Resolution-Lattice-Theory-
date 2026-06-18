# Research finding: the Wilson +1 direction without abstract group theory

**Problem.** Complete the Gauss–Wilson ±1 classification's hard side: the product
`P = ∏(units of ℤ/n)` is `≡ +1 (mod n)` when `n ∉ {1,2,4,pᵏ,2pᵏ}`. By the landed
`WilsonGeneralization.units_prod_eq_selfinv_prod`, `P ≡ ∏ S` where
`S = {x < n : x² ≡ 1 (mod n), gcd(x,n)=1}` (the square roots of 1). So the task is:
**`|S| ≥ 4 ⟹ ∏ S ≡ 1 (mod n)`**. Classically this is "the product of all elements of
an elementary-abelian 2-group of rank ≥ 2 is the identity" — but the corpus has no
abstract group theory, and the usual proof rides on `|S| = 2^m` (the order structure)
which is itself nontrivial ∅-axiom.

**The argument (∅-axiom-able, avoids the order structure).**
Let `P = ∏ S`, and let `t ∈ S` be any *nontrivial* element (`t ≠ 1`).

1. **Pairing.** The map `σ_t : s ↦ (s·t) mod n` is an involution on `S`
   (`σ_t² = id` since `t²≡1`) and is **fixed-point-free** (`s ≡ st ⟹ t ≡ 1`, false).
   So `S` partitions into pairs `{s, st}`, each with product `s·(st) = s²·t ≡ 1·t = t`.
   Hence **`P ≡ t^(|S|/2) (mod n)`** — for *every* nontrivial `t`. (Note this already
   forces `|S|` even.)

2. **Parity of `k := |S|/2` decides `t^k`.** Since `t² ≡ 1`,
   `t^k ≡ 1` if `k` even, `≡ t` if `k` odd.

3. **`|S| ≥ 4` forces `k` even.** Then `S` has ≥ 3 nontrivial elements; pick `t₁ ≠ t₂`,
   both nontrivial. From (1), `P ≡ t₁^k` and `P ≡ t₂^k`. If `k` were **odd**, (2) gives
   `t₁ ≡ P ≡ t₂` — contradicting `t₁ ≠ t₂`. So `k` is **even**, and
   `P ≡ t₁^k = (t₁²)^(k/2) ≡ 1`. ∎

**Why this is the right ∅-axiom route.** It never uses Lagrange, `|S| = 2^m`, or any
group axioms beyond what `S` concretely satisfies: closure (`a²≡1 ∧ b²≡1 ⟹ (ab)²≡1`),
commutativity of `· mod n`, and `t²≡1`. The only nontrivial machinery is the
**pairing-product computation `P ≡ t^(|S|/2)`**, which is exactly the
`WilsonGeneralization` involution-pairing toolkit (it already paired `S` by the
inverse-involution; here the involution is `·t` and each pair *accumulates* `t`
instead of cancelling to 1).

**Status.** Argument worked out (this note). Formalization: the pairing-accumulation
lemma `prodMod S ≡ t ^ (length S / 2)` is the one new piece; the rest is the
`t₁≠t₂ ∧ k odd → ⊥` finish. Combined with the existing `WilsonValue` (−1 side) and the
`SqrtOnePrimePower`/`SqrtOneTwoPrimePower` keystones, plus the CRT construction of a
nontrivial √1 for `n ∉ {1,2,4,pᵏ,2pᵏ}`, this closes the full classification.

**Companion remaining piece (the existence side).** `n ∉ {1,2,4,pᵏ,2pᵏ} ⟹ |S| ≥ 4`:
construct a nontrivial √1 via CRT — if `n = a·b`, `gcd(a,b)=1`, `a,b > 2`, then
`x ≡ 1 (mod a), x ≡ −1 (mod b)` (the corpus `CRTReconstruction.crtSolve`) is a √1 with
`x ≢ ±1 (mod n)`, giving a 4th element `{1, n−1, x, n−x}`. The case analysis that every
`n ∉ {1,2,4,pᵏ,2pᵏ}` admits such a coprime split (two odd prime factors, or `4∣n` with
an odd factor, or `8∣n`) is elementary but finicky.
