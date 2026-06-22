import E213.Lens.Number.Nat213.FTA

/-!
# Lens.Number.Nat213.Infinitude — Euclid's theorem over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, applied: with the FTA generated over `Nat213` (`FTA.fta`), another classical
theorem falls out *over the distinguishing's own carrier* — **Euclid's theorem**, the infinitude of
irreducibles: no finite list of irreducibles is complete (`infinitude_of_irreducibles`).

This is the descent leg doing what §7.1 calls primacy — *breadth*: the residue, read as `Nat213`,
reproduces a *second* discipline-defining theorem (after the FTA itself) with no Lean `Nat`.  Euclid's
classic argument, native: from a finite list `L` form `succ (prod L)`; it has an irreducible factor
`q` (`exists_factorization`), and `q ∈ L` would force `q ∣ prod L` and `q ∣ succ (prod L)`, hence
`q ∣ 1`, i.e. `q = 1` — impossible for an irreducible.  ∅-axiom.
-/

namespace E213.Lens.Number.Nat213.Infinitude

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (mul add one succ add_one_right mul_add add_left_cancel succ_ne_one)
open E213.Lens.Number.Nat213.Order (lt)
open E213.Lens.Number.Nat213.Divisibility
  (Dvd dvd_mul_right dvd_mul_of_dvd_right mul_eq_one)
open E213.Lens.Number.Nat213.Irreducible (Irreducible)
open E213.Lens.Number.Nat213.Factorization (prod not_mem_nil exists_factorization)
open E213.Lens.Number.Nat213.EuclidUnique (lt_of_mul_lt_mul_left)

/-- A list member divides the product of the list. -/
theorem mem_dvd_prod : ∀ {L : List Nat213} {q : Nat213}, q ∈ L → Dvd q (prod L)
  | [], _, h => absurd h not_mem_nil
  | a :: l, q, h => by
      cases h with
      | head => exact dvd_mul_right a (prod l)
      | tail _ h' => exact dvd_mul_of_dvd_right (mem_dvd_prod h') a

/-- **Coprimality of consecutive elements**: `q ∣ P` and `q ∣ succ P ⟹ q = 1` — `q` divides their
    difference `1`.  Native: `succ P = P + 1`, so `q·a + 1 = q·b` forces `q·k = 1` (`a < b`), hence
    `q = 1` (`mul_eq_one`).  No subtraction operator — the difference is the `lt`-witness. -/
theorem dvd_succ_self_imp_one {q P : Nat213} (h1 : Dvd q P) (h2 : Dvd q (succ P)) : q = one := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hkey : add (mul q a) one = mul q b := by rw [← ha, add_one_right]; exact hb
  obtain ⟨k, hbk⟩ := lt_of_mul_lt_mul_left (show lt (mul q a) (mul q b) from ⟨one, hkey⟩)
  have hcancel : add (mul q a) one = add (mul q a) (mul q k) := by
    rw [hkey, ← hbk, mul_add]
  exact (mul_eq_one (add_left_cancel hcancel).symm).1

/-- ★★★ **Euclid's theorem over the Raw-generated ℕ₊**: for *any* finite list of irreducibles there
    is an irreducible not in it — the irreducibles are unbounded.  Generated over `Nat213`, the
    distinguishing's own counting object; a second discipline-defining theorem after the FTA. -/
theorem infinitude_of_irreducibles (L : List Nat213) (hL : ∀ p, p ∈ L → Irreducible p) :
    ∃ q, Irreducible q ∧ q ∉ L := by
  obtain ⟨L', hL'irr, hL'prod⟩ := exists_factorization (succ (prod L))
  cases L' with
  | nil => exact absurd hL'prod.symm (succ_ne_one (prod L))
  | cons q L'' =>
      refine ⟨q, hL'irr q (List.Mem.head _), ?_⟩
      intro hqL
      have hqP : Dvd q (prod L) := mem_dvd_prod hqL
      have hqSP : Dvd q (succ (prod L)) := by
        rw [← hL'prod]; exact mem_dvd_prod (List.Mem.head _)
      exact (hL'irr q (List.Mem.head _)).1 (dvd_succ_self_imp_one hqP hqSP)

end E213.Lens.Number.Nat213.Infinitude
