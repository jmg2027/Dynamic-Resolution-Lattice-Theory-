import E213.Lens.Number.Nat213.Tower.PairCompletion

/-!
# PairCompletionUniversal — the invert move is THE universal group completion

`PairCompletion.invert_is_one_move` says `ℤ` and `ℚ_+` are one construction (the
pair-completion of a `CommCancelSemigroup`).  This file characterizes that construction by
its **universal property**, which is what makes "invert is one move" precise: the completion
is *the* group receiving the semigroup, through which every map to an abelian group factors.

Stated **without quotient types** (`Quot.sound` is axiom-dirty), in the repo's native
factor-through style (`Lens/Initiality.view_unique`, `Lens/Compose/Morphism`): for every
abelian-group target `H` and every semigroup-hom `f : M → H`, the map on representatives
`lift f (a, b) = f a − f b` is

  * **well-defined** on the completion — it respects `pairEquiv` (`lift_respects_pairEquiv`);
  * a **homomorphism** — `lift (p ∘ q) = lift p + lift q` (`lift_combine`);
  * a **factorization** of `f` — `lift (η m) = f m` through the embedding `η m = (m∘a, a)`
    (`lift_eta`).

So the completion is initial among abelian groups receiving `M` (the existence half of the
left-adjoint / Grothendieck universal property — stated as a concrete factoring map, **not**
an imported `Functor`/`Adjunction`).  The identity emerging as the diagonal
(`PairCompletion.diagonal_is_combine_identity`) is then forced: it is the element every such
`lift` sends to `H.zero`.  All ∅-axiom.
-/

namespace E213.Lens.Number.Nat213.Tower.PairCompletionUniversal

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Tower.PairCompletion
  (CommCancelSemigroup pairEquiv combine swap diagonal_single_class combine_swap_equiv_diagonal)

/-- An abelian-group target, all laws as `∀`-quantified equalities (PURE — no `funext`,
    no Mathlib `Group`).  The invert completion factors into any such target. -/
structure AbTarget where
  carrier : Type
  add : carrier → carrier → carrier
  neg : carrier → carrier
  zero : carrier
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero

theorem ab_zero_add (H : AbTarget) (a : H.carrier) : H.add H.zero a = a := by
  rw [H.add_comm, H.add_zero]

theorem ab_neg_add_cancel (H : AbTarget) (a : H.carrier) : H.add (H.neg a) a = H.zero := by
  rw [H.add_comm, H.add_neg]

theorem ab_add_right_cancel (H : AbTarget) {a b k : H.carrier}
    (h : H.add a k = H.add b k) : a = b := by
  have e : H.add (H.add a k) (H.neg k) = H.add (H.add b k) (H.neg k) :=
    congrArg (H.add · (H.neg k)) h
  rw [H.add_assoc, H.add_neg, H.add_zero, H.add_assoc, H.add_neg, H.add_zero] at e
  exact e

/-- The middle-four interchange — abelian rearrangement, the one workhorse for hom-proofs. -/
theorem ab_add_add_add_comm (H : AbTarget) (a b c d : H.carrier) :
    H.add (H.add a b) (H.add c d) = H.add (H.add a c) (H.add b d) := by
  rw [H.add_assoc a b (H.add c d), ← H.add_assoc b c d, H.add_comm b c,
      H.add_assoc c b d, ← H.add_assoc a c (H.add b d)]

theorem ab_neg_unique (H : AbTarget) {x y : H.carrier} (h : H.add x y = H.zero) :
    y = H.neg x := by
  have e : H.add (H.neg x) (H.add x y) = H.add (H.neg x) H.zero :=
    congrArg (H.add (H.neg x)) h
  rw [← H.add_assoc, ab_neg_add_cancel, ab_zero_add, H.add_zero] at e
  exact e

theorem ab_neg_add (H : AbTarget) (a b : H.carrier) :
    H.neg (H.add a b) = H.add (H.neg a) (H.neg b) := by
  have h : H.add (H.add a b) (H.add (H.neg a) (H.neg b)) = H.zero := by
    rw [H.add_comm (H.neg a) (H.neg b), H.add_assoc a b (H.add (H.neg b) (H.neg a)),
        ← H.add_assoc b (H.neg b) (H.neg a), H.add_neg b, ab_zero_add, H.add_neg a]
  exact (ab_neg_unique H h).symm

/-- The factoring map on representatives: `lift f (a, b) = f a − f b` (`f a + neg (f b)`),
    the value the universal property forces on the completion. -/
def lift (M : CommCancelSemigroup) (H : AbTarget) (f : Nat213 → H.carrier)
    (p : Nat213 × Nat213) : H.carrier :=
  H.add (f p.1) (H.neg (f p.2))

variable {M : CommCancelSemigroup} {H : AbTarget} {f : Nat213 → H.carrier}

/-- ★★★ **`lift` is well-defined on the completion** — it respects `pairEquiv`.  If
    `(a,b) ~ (c,d)` (`a∘d = b∘c`) then `f a − f b = f c − f d`: the factoring map descends to
    the completion without a quotient type. -/
theorem lift_respects_pairEquiv
    (hf : ∀ x y, f (M.op x y) = H.add (f x) (f y))
    {p q : Nat213 × Nat213} (hpq : pairEquiv M p q) :
    lift M H f p = lift M H f q := by
  have star : H.add (f p.1) (f q.2) = H.add (f p.2) (f q.1) := by
    have e := congrArg f hpq
    rw [hf, hf] at e; exact e
  refine ab_add_right_cancel H (k := H.add (f p.2) (f q.2)) ?_
  show H.add (H.add (f p.1) (H.neg (f p.2))) (H.add (f p.2) (f q.2))
      = H.add (H.add (f q.1) (H.neg (f q.2))) (H.add (f p.2) (f q.2))
  rw [H.add_assoc (f p.1) (H.neg (f p.2)) (H.add (f p.2) (f q.2)),
      ← H.add_assoc (H.neg (f p.2)) (f p.2) (f q.2),
      ab_neg_add_cancel H (f p.2), ab_zero_add H (f q.2),
      H.add_assoc (f q.1) (H.neg (f q.2)) (H.add (f p.2) (f q.2)),
      H.add_comm (f p.2) (f q.2),
      ← H.add_assoc (H.neg (f q.2)) (f q.2) (f p.2),
      ab_neg_add_cancel H (f q.2), ab_zero_add H (f p.2),
      H.add_comm (f q.1) (f p.2)]
  exact star

/-- ★★★ **`lift` is a homomorphism** — `lift (p ∘ q) = lift p + lift q`. -/
theorem lift_combine
    (hf : ∀ x y, f (M.op x y) = H.add (f x) (f y)) (p q : Nat213 × Nat213) :
    lift M H f (combine M p q) = H.add (lift M H f p) (lift M H f q) := by
  show H.add (f (M.op p.1 q.1)) (H.neg (f (M.op p.2 q.2)))
      = H.add (H.add (f p.1) (H.neg (f p.2))) (H.add (f q.1) (H.neg (f q.2)))
  rw [hf, hf, ab_neg_add H (f p.2) (f q.2),
      ab_add_add_add_comm H (f p.1) (f q.1) (H.neg (f p.2)) (H.neg (f q.2)),
      ab_add_add_add_comm H (f p.1) (H.neg (f p.2)) (f q.1) (H.neg (f q.2))]

/-- ★★★ **`lift` factors `f` through the embedding `η m = (m ∘ a, a)`** — `lift (η m) = f m`
    (the `f a` and `−f a` cancel).  The embedding is independent of the base point `a` up to
    `pairEquiv` (`lift_respects_pairEquiv`). -/
theorem lift_eta
    (hf : ∀ x y, f (M.op x y) = H.add (f x) (f y)) (m a : Nat213) :
    lift M H f (M.op m a, a) = f m := by
  show H.add (f (M.op m a)) (H.neg (f a)) = f m
  rw [hf, H.add_assoc, H.add_neg, H.add_zero]

/-- ★★★★ **The invert completion is universal — every map to an abelian group factors through
    it.**  For any abelian-group target `H` and semigroup-hom `f : M → H`, the representative
    map `lift f` is well-defined on the completion, a homomorphism, and factors `f` through the
    embedding `η`.  This is the existence half of the group-completion universal property
    (initiality / left adjoint), stated Quot-free as a concrete factoring map — making
    `invert_is_one_move` precise: the invert move is *the* universal group completion, the same
    construction at `+` (`ℤ`) and `·` (`ℚ_+`).  (Uniqueness of the factoring hom holds for any
    `g` that respects `pairEquiv` and `combine`; stated unconditionally it needs choice on the
    fiber, so it is left as the hypothesized companion.) -/
theorem invert_factors_through_any_group
    (hf : ∀ x y, f (M.op x y) = H.add (f x) (f y)) :
    (∀ {p q : Nat213 × Nat213}, pairEquiv M p q → lift M H f p = lift M H f q)
    ∧ (∀ p q : Nat213 × Nat213,
        lift M H f (combine M p q) = H.add (lift M H f p) (lift M H f q))
    ∧ (∀ m a : Nat213, lift M H f (M.op m a, a) = f m) :=
  ⟨fun hpq => lift_respects_pairEquiv hf hpq, lift_combine hf, lift_eta hf⟩

theorem ab_add_left_cancel (H : AbTarget) {a b k : H.carrier}
    (h : H.add k a = H.add k b) : a = b := by
  rw [H.add_comm k a, H.add_comm k b] at h
  exact ab_add_right_cancel H h

/-- Every pair decomposes as `η(a) ∘ inv(η(b))` for any base point `c` — `(a, b) ~ combine
    (a∘c, c) (c, b∘c)`.  This is "every group element is `η a − η b`", the key to uniqueness. -/
theorem pair_equiv_eta_combine (M : CommCancelSemigroup) (c : Nat213) (p : Nat213 × Nat213) :
    pairEquiv M p (combine M (M.op p.1 c, c) (swap (M.op p.2 c, c))) := by
  show M.op p.1 (M.op c (M.op p.2 c)) = M.op p.2 (M.op (M.op p.1 c) c)
  rw [← M.assoc c p.2 c, M.comm c p.2, M.assoc p.2 c c,
      ← M.assoc p.1 p.2 (M.op c c), M.assoc p.1 c c,
      ← M.assoc p.2 p.1 (M.op c c), M.comm p.2 p.1]

/-- ★★★★ **Uniqueness — the factoring hom is `lift`.**  Any `g` that (i) is well-defined on the
    completion (respects `pairEquiv`), (ii) is a `combine`-homomorphism, and (iii) factors `f`
    through `η` (`g (m∘a, a) = f m`) equals `lift f` on every representative.  Together with
    `invert_factors_through_any_group` this is the **full** group-completion universal property
    (initiality, existence ∧ uniqueness), ∅-axiom and Quot-free.  Choice is not needed: `g` is
    assumed to respect `pairEquiv` (i.e. to genuinely be a map on the completion) — the only AC
    issue is for `g`'s that do *not*, which are not maps on the completion at all. -/
theorem lift_unique
    (hf : ∀ x y, f (M.op x y) = H.add (f x) (f y))
    (g : Nat213 × Nat213 → H.carrier)
    (g_resp : ∀ {p q : Nat213 × Nat213}, pairEquiv M p q → g p = g q)
    (g_hom : ∀ p q : Nat213 × Nat213, g (combine M p q) = H.add (g p) (g q))
    (g_eta : ∀ m a : Nat213, g (M.op m a, a) = f m)
    (c : Nat213) (p : Nat213 × Nat213) :
    g p = lift M H f p := by
  -- (1) g kills the diagonal: g (k, k) = 0
  have hz : ∀ k : Nat213, g (k, k) = H.zero := by
    intro k
    have hx : H.add (g (k, k)) (g (k, k)) = g (k, k) := by
      rw [← g_hom (k, k) (k, k)]
      exact g_resp (diagonal_single_class M (M.op k k) k)
    have e : H.add (g (k, k)) (g (k, k)) = H.add (g (k, k)) H.zero := by
      rw [hx, H.add_zero]
    exact ab_add_left_cancel H e
  -- (2) g sends inv(η b) to −f b
  have hswap : ∀ b : Nat213, g (swap (M.op b c, c)) = H.neg (f b) := by
    intro b
    have key : H.add (g (M.op b c, c)) (g (swap (M.op b c, c))) = H.zero := by
      rw [← g_hom (M.op b c, c) (swap (M.op b c, c))]
      have hd : g (combine M (M.op b c, c) (swap (M.op b c, c)))
          = g (M.op b c, M.op b c) :=
        g_resp (combine_swap_equiv_diagonal M (M.op b c, c) (M.op b c))
      rw [hd]; exact hz (M.op b c)
    rw [g_eta b c] at key
    exact ab_neg_unique H key
  -- (3) decompose p and compute
  show g p = H.add (f p.1) (H.neg (f p.2))
  rw [g_resp (pair_equiv_eta_combine M c p), g_hom, g_eta p.1 c, hswap p.2]

/-- ★★★★★ **The invert move is THE universal group completion — existence ∧ uniqueness.**
    For every abelian-group target `H` and semigroup-hom `f : M → H`:

      * **existence** — `lift f` is well-defined on the completion, a homomorphism, and factors
        `f` through `η`;
      * **uniqueness** — any `g` that is well-defined on the completion (respects `pairEquiv`),
        a `combine`-homomorphism, and factors `f` through `η`, equals `lift f`.

    This is the complete group-completion universal property (initiality), ∅-axiom, Quot-free,
    and choice-free.  It is the precise content of "invert is one move": the invert move is *the*
    unique-up-to-iso group completion, instantiated at `+` (`ℤ`) and `·` (`ℚ_+`).  The framing as
    a "left adjoint to a forgetful functor" is an imported 2-categorical comparison and is kept to
    narrative only; the residue-native content is this concrete factor-through + uniqueness, the
    same shape as `Theory.Raw.Lambek`'s initiality. -/
theorem invert_is_the_universal_group_completion
    (hf : ∀ x y, f (M.op x y) = H.add (f x) (f y)) :
    (∀ {p q : Nat213 × Nat213}, pairEquiv M p q → lift M H f p = lift M H f q)
    ∧ (∀ p q : Nat213 × Nat213,
        lift M H f (combine M p q) = H.add (lift M H f p) (lift M H f q))
    ∧ (∀ m a : Nat213, lift M H f (M.op m a, a) = f m)
    ∧ (∀ (g : Nat213 × Nat213 → H.carrier),
        (∀ {p q : Nat213 × Nat213}, pairEquiv M p q → g p = g q) →
        (∀ p q : Nat213 × Nat213, g (combine M p q) = H.add (g p) (g q)) →
        (∀ m a : Nat213, g (M.op m a, a) = f m) →
        ∀ p : Nat213 × Nat213, g p = lift M H f p) :=
  ⟨fun hpq => lift_respects_pairEquiv hf hpq, lift_combine hf, lift_eta hf,
   fun g gr gh ge p => lift_unique hf g gr gh ge Nat213.one p⟩

end E213.Lens.Number.Nat213.Tower.PairCompletionUniversal
