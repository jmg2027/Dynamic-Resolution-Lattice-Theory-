import E213.Meta.Tactic.NatHelper
open E213.Tactic.NatHelper

/-!
# Combinatorial arity: `k ≥ 3` is vacuous over `Fin 2` base

★★★★★★★★★★★★★★★ **Generic pigeonhole closing the
"arity = 2" leg of the atomic signature forcing chain.** ★★★★★★★★★★★★★★★

Companion to `ArityForcing.lean` (which proves the k = 3 case
concretely): this file proves the **uniform pigeonhole** that
any function `f : Fin k → Fin 2` with `k ≥ 3` has a collision.
Consequence: a signature with a k-arity relation symbol
requiring pairwise-distinct `Fin 2` arguments has no Reachable
relation-term for any `k ≥ 3`.

Combined with the k = 0, 1 degeneracy (signatures themselves
preclude tree structure or distinguishing), this closes the
"k = 2 is the unique non-degenerate, non-vacuous arity for the
`Fin 2` base" leg of the atomic forcing chain — the 4th
dimension to be Lean-formalised, alongside
`PairForcing.lean` (the (NS, NT) = (3, 2) shape),
`OrbitForcing.lean` (the d = 5 dimension), and
`Five.lean` (the atomic-iff-five bridge).

## Strategy

The k = 3 case in `ArityForcing.lean` uses a 6-way `match` over
`cases_lt_two`.  The general k ≥ 3 case is reduced to the same
pigeonhole structurally: pick any three indices `i, j, l : Fin k`
(possible because `k ≥ 3`), apply `cases_lt_two` to each of
`(f i).val, (f j).val, (f l).val`, and derive the contradiction.

STRICT ∅-AXIOM.
-/

namespace E213.Theory.Atomicity.CombinatorialArity

/-! ## §1 — Pigeonhole: Fin k → Fin 2 collides for k ≥ 3 -/

/-- Three indices `0, 1, 2` exist in `Fin k` when `k ≥ 3`.  Used to
    extract three witnesses for the pigeonhole argument. -/
def fin_of_lt_3 (k : Nat) (hk : 3 ≤ k) (i : Nat) (hi : i < 3) : Fin k :=
  ⟨i, Nat.lt_of_lt_of_le hi hk⟩

/-- Three indices `⟨0, ⟨1, ⟨2 : Fin k`, pairwise distinct. -/
private theorem fin_of_lt_3_distinct (k : Nat) (hk : 3 ≤ k) :
    (fin_of_lt_3 k hk 0 (by decide)) ≠ (fin_of_lt_3 k hk 1 (by decide))
    ∧ (fin_of_lt_3 k hk 1 (by decide)) ≠ (fin_of_lt_3 k hk 2 (by decide))
    ∧ (fin_of_lt_3 k hk 0 (by decide)) ≠ (fin_of_lt_3 k hk 2 (by decide)) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;>
    exact absurd (Fin.mk.inj h) (by decide)

/-- ★ **Pigeonhole** ★: any function `f : Fin k → Fin 2` with
    `k ≥ 3` has two distinct inputs sharing a value.  This is the
    structural content of "k = 2 is unique" in the atomic
    forcing chain. -/
theorem pigeonhole_fin_to_fin2 (k : Nat) (hk : 3 ≤ k) (f : Fin k → Fin 2) :
    ∃ i j : Fin k, i ≠ j ∧ f i = f j := by
  let a : Fin k := fin_of_lt_3 k hk 0 (by decide)
  let b : Fin k := fin_of_lt_3 k hk 1 (by decide)
  let c : Fin k := fin_of_lt_3 k hk 2 (by decide)
  obtain ⟨hab, hbc, hac⟩ := fin_of_lt_3_distinct k hk
  have h_fa : (f a).val < 2 := (f a).isLt
  have h_fb : (f b).val < 2 := (f b).isLt
  have h_fc : (f c).val < 2 := (f c).isLt
  match cases_lt_two h_fa, cases_lt_two h_fb, cases_lt_two h_fc with
  | Or.inl ha0, Or.inl hb0, _ =>
      exact ⟨a, b, hab, Fin.ext (ha0.trans hb0.symm)⟩
  | Or.inr ha1, Or.inr hb1, _ =>
      exact ⟨a, b, hab, Fin.ext (ha1.trans hb1.symm)⟩
  | _, Or.inl hb0, Or.inl hc0 =>
      exact ⟨b, c, hbc, Fin.ext (hb0.trans hc0.symm)⟩
  | _, Or.inr hb1, Or.inr hc1 =>
      exact ⟨b, c, hbc, Fin.ext (hb1.trans hc1.symm)⟩
  | Or.inl ha0, _, Or.inl hc0 =>
      exact ⟨a, c, hac, Fin.ext (ha0.trans hc0.symm)⟩
  | Or.inr ha1, _, Or.inr hc1 =>
      exact ⟨a, c, hac, Fin.ext (ha1.trans hc1.symm)⟩

/-! ## §2 — Generic Raw_k signature

For ANY `k`, define `Raw k` with a `k`-ary `rel` constructor (built
on `Fin k → Raw k` so the arity is type-level explicit) and a
`Fin 2` base.  This subsumes `ArityForcing.Raw3` (the concrete
k = 3 instance) as a parametric family. -/

/-- Raw signature with `k`-arity relation.  The arity is fixed at
    the type level via the `Fin k → Raw k` argument to `rel`. -/
inductive Raw (k : Nat) where
  | object : Fin 2 → Raw k
  | rel : (Fin k → Raw k) → Raw k

/-- Reachable predicate for k-arity Raw: the k arguments of every
    `rel` must be pairwise distinct (the analogue of the
    `x ≠ y → y ≠ z → x ≠ z` triple in `Reachable3`). -/
inductive Reachable (k : Nat) : Raw k → Prop where
  | base : (i : Fin 2) → Reachable k (.object i)
  | step (xs : Fin k → Raw k) :
      (∀ i, Reachable k (xs i)) →
      (∀ i j : Fin k, i ≠ j → xs i ≠ xs j) →
      Reachable k (.rel xs)

/-! ## §3 — Vacuousness theorem for k ≥ 3 -/

/-- For `k ≥ 3`, every Reachable Raw term is a base object —
    the `rel` step constructor never fires because its
    `xs : Fin k → Raw k` would need `k` pairwise-distinct
    `Fin 2`-objects, contradicting pigeonhole on three indices.

    Proved in-line over three indices `a, b, c : Fin k` rather
    than building a Fin 2 witness function (which would require
    `Classical.choice`).  Each `xs a`, `xs b`, `xs c` is destructured
    constructively from the inductive hypothesis. -/
theorem reachable_only_object (k : Nat) (hk : 3 ≤ k)
    {x : Raw k} (h : Reachable k x) :
    ∃ i : Fin 2, x = .object i := by
  induction h with
  | base i => exact ⟨i, rfl⟩
  | @step xs _ h_distinct ih =>
      exfalso
      let a : Fin k := fin_of_lt_3 k hk 0 (by decide)
      let b : Fin k := fin_of_lt_3 k hk 1 (by decide)
      let c : Fin k := fin_of_lt_3 k hk 2 (by decide)
      obtain ⟨hab, hbc, hac⟩ := fin_of_lt_3_distinct k hk
      obtain ⟨va, ha_eq⟩ := ih a
      obtain ⟨vb, hb_eq⟩ := ih b
      obtain ⟨vc, hc_eq⟩ := ih c
      have h_va_lt : va.val < 2 := va.isLt
      have h_vb_lt : vb.val < 2 := vb.isLt
      have h_vc_lt : vc.val < 2 := vc.isLt
      -- Pigeonhole: three Fin 2 values, two must collide.
      match cases_lt_two h_va_lt, cases_lt_two h_vb_lt, cases_lt_two h_vc_lt with
      | Or.inl ha0, Or.inl hb0, _ =>
          apply h_distinct a b hab
          rw [ha_eq, hb_eq, Fin.ext (ha0.trans hb0.symm)]
      | Or.inr ha1, Or.inr hb1, _ =>
          apply h_distinct a b hab
          rw [ha_eq, hb_eq, Fin.ext (ha1.trans hb1.symm)]
      | _, Or.inl hb0, Or.inl hc0 =>
          apply h_distinct b c hbc
          rw [hb_eq, hc_eq, Fin.ext (hb0.trans hc0.symm)]
      | _, Or.inr hb1, Or.inr hc1 =>
          apply h_distinct b c hbc
          rw [hb_eq, hc_eq, Fin.ext (hb1.trans hc1.symm)]
      | Or.inl ha0, _, Or.inl hc0 =>
          apply h_distinct a c hac
          rw [ha_eq, hc_eq, Fin.ext (ha0.trans hc0.symm)]
      | Or.inr ha1, _, Or.inr hc1 =>
          apply h_distinct a c hac
          rw [ha_eq, hc_eq, Fin.ext (ha1.trans hc1.symm)]

/-- Corollary: for `k ≥ 3`, no `rel`-term is Reachable. -/
theorem no_reachable_rel (k : Nat) (hk : 3 ≤ k) (xs : Fin k → Raw k) :
    ¬ Reachable k (.rel xs) := by
  intro h
  obtain ⟨_, hi⟩ := reachable_only_object k hk h
  cases hi

/-! ## §4 — Atomic forcing capstone: arity = 2 is unique

For each `k ∈ {0, 1, 3, 4, …}`, the signature with `k`-arity `rel`
and `Fin 2` base fails to support non-vacuous, non-degenerate
recursion:

  · `k = 0`: `rel : Raw → Raw` (constant) — no recursion.
  · `k = 1`: `rel : Raw → Raw` (unary, no distinct constraint) —
    linear chain, no distinguishing.
  · `k ≥ 3`: vacuous by `no_reachable_rel` (this file).

The k=0, 1 degeneracy is structural (visible from the signature
itself); the k ≥ 3 vacuousness is the substantive forcing.  Hence
**k = 2** is the unique value supporting non-degenerate,
non-vacuous self-referential recursion over `Fin 2` —
the 4th atomic-signature dimension forced parametrically. -/

/-- ★ **Capstone**: `k = 2` is structurally unique for non-vacuous,
    non-degenerate self-reference over `Fin 2`.  Stated as a
    bundle: ∀ k ≥ 3, no `rel`-term is Reachable. -/
theorem arity_2_unique_via_k_ge_3_vacuous :
    ∀ (k : Nat), 3 ≤ k →
      ∀ (xs : Fin k → Raw k), ¬ Reachable k (.rel xs) :=
  no_reachable_rel

end E213.Theory.Atomicity.CombinatorialArity
