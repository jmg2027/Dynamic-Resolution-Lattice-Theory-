/-
Rederive/EventPrimary.lean — the event-primary formalization (Design P,
SPEC §1 F-ev, Q4).  Theory counterpart: rederive/theory/event_primary_design.md.

ORIGIN_RAW §2 says `a`, `b` are *not objects* — "objects are not defined
yet; only the difference is."  Taken literally, the carrier is the
distinction itself, and "points" are derived reifications.  Design P (the
design doc §2.3) realizes this:

  * The carrier `Ev` is the family of distinction-*terms*.  Its operands
    are either one of two formal **pole tags** (`Pole.l`, `Pole.r` — the
    two roles of the primordial contrast, NOT carrier elements) or an
    earlier distinction (a completed distinction in operand position =
    the derived "point").
  * `prim = pp l r` is the unique element constructible with no earlier
    distinction: the first distinction (R3).
  * Canonicity (`canon`) handles unorderedness and no-self-pair by
    canonical representatives — NO quotient (R6; Quot.sound forbidden).

Implementation note (order transport).  Design §3 states the `Ev` term
order is "the F-ev counterpart of whatever tie-break F-obj's canonical
`Tree` uses."  We take that literally: the strictness clause of `canon`
for `ee` is read off the object order `Tree.cmp` under the translation
`evToTree`.  This keeps the whole file axiom-free with no well-founded
recursion, and is exactly the design-sanctioned tie-break.  (An intrinsic
`Ev.cmp` is possible but buys nothing the transported order does not.)

Main results:
  * Carrier `Ev`/`D` (Design P), `beq`/`DecidableEq`, `size`, `prim`.
  * Translations `evToTree`/`opToTree`  ⇄  `treeToOperand`/`treeToEv`.
  * `treeToOperand_evToTree` + `opToTree_treeToOperand`: the two
    round-trips — a bijection between canonical distinction-terms and
    canonical trees (the F-ev *operand* sort ≅ F-obj `Tree`, §7.1).
  * `evToTree_injective`, `evToTree_canonB`, `evToTree_composite`:
    faithfulness + image characterization + "a distinction is never an
    atom".
  * `prim_subterm` (R3 as a theorem) with the F-obj non-analogue
    (`no_universal_atom`): the event-primacy asymmetry A1 — F-ev has a
    least element below every distinction, F-obj has none.

Zero dependencies beyond Rederive.Tree; Lean 4 core only.  Every theorem
is verified axiom-free in Rederive/AxiomCheck.lean.
-/

import Rederive.Tree

namespace Rederive

namespace FEv

/-! ## 0. Boolean `and` splitting (axiom-free; core lemma carries propext) -/

theorem band_split {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  cases x with
  | true => exact ⟨rfl, h⟩
  | false => exact Bool.noConfusion h

theorem band_join {x y : Bool} (h₁ : x = true) (h₂ : y = true) : (x && y) = true := by
  subst h₁; exact h₂

/-! ## 1. Poles — the two roles of the primordial contrast (tags, not a carrier) -/

/-- The two roles of the primordial contrast.  Tags, never inhabitants of
the carrier `Ev` (requirement R2). -/
inductive Pole : Type where
  | l : Pole
  | r : Pole

/-- Structural boolean equality on poles. -/
def Pole.beq : Pole → Pole → Bool
  | .l, .l => true
  | .r, .r => true
  | _, _ => false

theorem Pole.beq_refl : ∀ p : Pole, Pole.beq p p = true
  | .l => rfl
  | .r => rfl

theorem Pole.eq_of_beq : ∀ {p q : Pole}, Pole.beq p q = true → p = q
  | .l, .l, _ => rfl
  | .r, .r, _ => rfl
  | .l, .r, h => Bool.noConfusion h
  | .r, .l, h => Bool.noConfusion h

instance : DecidableEq Pole := fun p q =>
  match hb : Pole.beq p q with
  | true => isTrue (Pole.eq_of_beq hb)
  | false => isFalse (fun h => by rw [h, Pole.beq_refl] at hb; exact Bool.noConfusion hb)

/-! ## 2. The carrier of distinction-terms (Design P §3) -/

/-- Raw distinction-terms.  The operand sum (`Pole ⊕ earlier-distinction`)
is flattened into three constructors to stay first-order:
  * `pp p q` — both operands are poles;
  * `pe p e` — one pole, one earlier distinction;
  * `ee d e` — two earlier distinctions.
Unorderedness / no-self-pair are imposed by `canon` (below), NOT by a
quotient. -/
inductive Ev : Type where
  | pp : Pole → Pole → Ev
  | pe : Pole → Ev → Ev
  | ee : Ev → Ev → Ev

/-- Structural boolean equality on `Ev`. -/
def Ev.beq : Ev → Ev → Bool
  | .pp p q, .pp p' q' => Pole.beq p p' && Pole.beq q q'
  | .pe p e, .pe p' e' => Pole.beq p p' && Ev.beq e e'
  | .ee d e, .ee d' e' => Ev.beq d d' && Ev.beq e e'
  | _, _ => false

theorem Ev.beq_refl : ∀ e : Ev, Ev.beq e e = true
  | .pp p q => by simp only [Ev.beq]; rw [Pole.beq_refl, Pole.beq_refl]; rfl
  | .pe p e => by simp only [Ev.beq]; rw [Pole.beq_refl, Ev.beq_refl e]; rfl
  | .ee d e => by simp only [Ev.beq]; rw [Ev.beq_refl d, Ev.beq_refl e]; rfl

theorem Ev.eq_of_beq : ∀ {d e : Ev}, Ev.beq d e = true → d = e
  | .pp p q, .pp p' q', h => by
    have hs := band_split h
    rw [Pole.eq_of_beq hs.1, Pole.eq_of_beq hs.2]
  | .pe p e, .pe p' e', h => by
    have hs := band_split h
    rw [Pole.eq_of_beq hs.1, Ev.eq_of_beq hs.2]
  | .ee d e, .ee d' e', h => by
    have hs := band_split h
    rw [Ev.eq_of_beq hs.1, Ev.eq_of_beq hs.2]
  | .pp _ _, .pe _ _, h => Bool.noConfusion h
  | .pp _ _, .ee _ _, h => Bool.noConfusion h
  | .pe _ _, .pp _ _, h => Bool.noConfusion h
  | .pe _ _, .ee _ _, h => Bool.noConfusion h
  | .ee _ _, .pp _ _, h => Bool.noConfusion h
  | .ee _ _, .pe _ _, h => Bool.noConfusion h

instance : DecidableEq Ev := fun d e =>
  match hb : Ev.beq d e with
  | true => isTrue (Ev.eq_of_beq hb)
  | false => isFalse (fun h => by rw [h, Ev.beq_refl] at hb; exact Bool.noConfusion hb)

/-- Number of `Ev` nodes (Design §4.3). -/
def Ev.size : Ev → Nat
  | .pp _ _ => 1
  | .pe _ e => Ev.size e + 1
  | .ee d e => Ev.size d + Ev.size e + 1

/-! ## 3. Translation to the object-primary carrier (Design §7.1)

The maps are defined FIRST (they carry no dependency on `canon`), so that
`canon`'s strictness clause for `ee` may read the object order off the
translation — the design-sanctioned order transport. -/

/-- A pole translates to its atom role. -/
def poleToTree : Pole → Tree
  | .l => Tree.a
  | .r => Tree.b

/-- A distinction-term translates to the composite tree it names.  The
`Tree.pairing` smart constructor sorts, so `evToTree` always lands on a
sorted (canonical) tree and is a *node* (never an atom). -/
def evToTree : Ev → Tree
  | .pp p q => Tree.pairing (poleToTree p) (poleToTree q)
  | .pe p e => Tree.pairing (poleToTree p) (evToTree e)
  | .ee d e => Tree.pairing (evToTree d) (evToTree e)

/-- An operand (`Pole ⊕ Ev`) translates: a pole to its atom, a
distinction to its composite. -/
def opToTree : Pole ⊕ Ev → Tree
  | .inl p => poleToTree p
  | .inr e => evToTree e

/-- Every distinction-term maps to a *node*. -/
theorem evToTree_node : ∀ e : Ev, ∃ x y, evToTree e = Tree.node x y := by
  intro e
  cases e with
  | pp p q =>
    show ∃ x y, Tree.pairing (poleToTree p) (poleToTree q) = Tree.node x y
    cases h : Tree.cmp (poleToTree p) (poleToTree q) with
    | lt => exact ⟨_, _, Tree.pairing_of_lt h⟩
    | gt => exact ⟨_, _, Tree.pairing_of_gt h⟩
    | eq => exact ⟨_, _, by rw [Tree.eq_of_cmp_eq _ _ h]; unfold Tree.pairing; rw [Tree.cmp_refl]⟩
  | pe p e =>
    show ∃ x y, Tree.pairing (poleToTree p) (evToTree e) = Tree.node x y
    cases h : Tree.cmp (poleToTree p) (evToTree e) with
    | lt => exact ⟨_, _, Tree.pairing_of_lt h⟩
    | gt => exact ⟨_, _, Tree.pairing_of_gt h⟩
    | eq => exact ⟨_, _, by rw [Tree.eq_of_cmp_eq _ _ h]; unfold Tree.pairing; rw [Tree.cmp_refl]⟩
  | ee d e =>
    show ∃ x y, Tree.pairing (evToTree d) (evToTree e) = Tree.node x y
    cases h : Tree.cmp (evToTree d) (evToTree e) with
    | lt => exact ⟨_, _, Tree.pairing_of_lt h⟩
    | gt => exact ⟨_, _, Tree.pairing_of_gt h⟩
    | eq => exact ⟨_, _, by rw [Tree.eq_of_cmp_eq _ _ h]; unfold Tree.pairing; rw [Tree.cmp_refl]⟩

/-- A pole's atom is strictly below any distinction's composite in the
object order (atoms sort before nodes). -/
theorem cmp_pole_ev (p : Pole) (e : Ev) : Tree.cmp (poleToTree p) (evToTree e) = .lt := by
  obtain ⟨x, y, he⟩ := evToTree_node e
  rw [he]; cases p <;> rfl

/-- Normal form of a `pe` translation: it is the node with the pole first. -/
theorem evToTree_pe (p : Pole) (e : Ev) :
    evToTree (Ev.pe p e) = Tree.node (poleToTree p) (evToTree e) := by
  show Tree.pairing (poleToTree p) (evToTree e) = _
  exact Tree.pairing_of_lt (cmp_pole_ev p e)

/-! ## 4. Canonicity, the carrier `D`, and the primordial element -/

/-- The object order, as a `Bool` "strictly less" test on `Ev` operands.
This is the transported strictness used by `canon` for `ee` (see header). -/
def ltEv (d e : Ev) : Bool :=
  match Tree.cmp (evToTree d) (evToTree e) with
  | .lt => true
  | _ => false

theorem ltEv_lt {d e : Ev} (h : ltEv d e = true) : Tree.cmp (evToTree d) (evToTree e) = .lt := by
  unfold ltEv at h
  cases hc : Tree.cmp (evToTree d) (evToTree e) with
  | lt => rfl
  | eq => rw [hc] at h; exact Bool.noConfusion h
  | gt => rw [hc] at h; exact Bool.noConfusion h

/-- Canonicity (Design §3).  Collapses distinctness + unorderedness +
no-self-pair into structural constraints:
  * `pp p q` canonical iff `p = l ∧ q = r` — the ONLY canonical pole-pole
    term is `prim` (distinctness and order both forced);
  * `pe p e` canonical iff `e` canonical — a pole never equals a
    distinction, so distinctness is automatic, and the pole is already
    first (sorted);
  * `ee d e` canonical iff both canonical AND strictly ordered — so a
    self-pair `⟨x,x⟩` has NO canonical term at all (C4 becomes
    non-existence, not a side condition). -/
def canon : Ev → Bool
  | .pp p q => Pole.beq p .l && Pole.beq q .r
  | .pe _ e => canon e
  | .ee d e => canon d && canon e && ltEv d e

/-- THE carrier: canonical distinction-terms (a subtype, NOT a quotient). -/
abbrev D : Type := { e : Ev // canon e = true }

/-- The first distinction `prim = ⟨pole l, pole r⟩` — the unique element
constructible with no earlier distinction (R3). -/
def D.prim : D := ⟨Ev.pp .l .r, rfl⟩

/-- Derived operand sort: a *defined* sum, not a new inductive (R4 — a
"point" is a completed distinction in operand position, or a pole role). -/
abbrev Operand : Type := Pole ⊕ D

/-! ## 5. The reverse translation (Design §7.1) -/

/-- Assemble an `Ev` from two operand translations (poles float to the
front so the result is well-formed for the `pe` shape). -/
def combine : Pole ⊕ Ev → Pole ⊕ Ev → Ev
  | .inl p, .inl q => Ev.pp p q
  | .inl p, .inr e => Ev.pe p e
  | .inr e, .inl q => Ev.pe q e
  | .inr d, .inr e => Ev.ee d e

/-- Object → operand.  Total: every tree is a pole role or a distinction. -/
def treeToOperand : Tree → Pole ⊕ Ev
  | .a => .inl .l
  | .b => .inl .r
  | .node x y => .inr (combine (treeToOperand x) (treeToOperand y))

/-- Object → distinction (partial: atoms are pole roles, not distinctions). -/
def treeToEv : Tree → Option Ev
  | .a => none
  | .b => none
  | .node x y => some (combine (treeToOperand x) (treeToOperand y))

theorem treeToOperand_pole (p : Pole) : treeToOperand (poleToTree p) = Sum.inl p := by
  cases p <;> rfl

/-- `evToTree` transports `combine` to `Tree.pairing` (needs `pairing_comm`
in the pole-after-distinction case). -/
theorem evToTree_combine (u v : Pole ⊕ Ev) :
    evToTree (combine u v) = Tree.pairing (opToTree u) (opToTree v) := by
  cases u with
  | inl p =>
    cases v with
    | inl q => rfl
    | inr e => rfl
  | inr d =>
    cases v with
    | inl q =>
      show evToTree (Ev.pe q d) = Tree.pairing (evToTree d) (poleToTree q)
      show Tree.pairing (poleToTree q) (evToTree d) = Tree.pairing (evToTree d) (poleToTree q)
      exact Tree.pairing_comm _ _
    | inr e => rfl

/-! ## 6. The round-trips: a bijection on canonical fragments (Design §7.1) -/

/-- **Round-trip F-ev → obj → F-ev** (a retraction): every canonical
distinction is recovered from its tree.  Immediately gives injectivity of
`evToTree` on `D`. -/
theorem treeToOperand_evToTree : ∀ e : Ev, canon e = true → treeToOperand (evToTree e) = Sum.inr e := by
  intro e
  induction e with
  | pp p q =>
    intro hc
    have hs := band_split hc
    have hp : p = .l := Pole.eq_of_beq hs.1
    have hq : q = .r := Pole.eq_of_beq hs.2
    subst hp; subst hq
    rfl
  | pe p e ih =>
    intro hc
    have hce : canon e = true := hc
    rw [evToTree_pe]
    show Sum.inr (combine (treeToOperand (poleToTree p)) (treeToOperand (evToTree e))) = _
    rw [treeToOperand_pole, ih hce]
    rfl
  | ee d e ihd ihe =>
    intro hc
    have hs := band_split hc
    have hs' := band_split hs.1
    have hcd : canon d = true := hs'.1
    have hce : canon e = true := hs'.2
    have hlt : Tree.cmp (evToTree d) (evToTree e) = .lt := ltEv_lt hs.2
    show treeToOperand (Tree.pairing (evToTree d) (evToTree e)) = _
    rw [Tree.pairing_of_lt hlt]
    show Sum.inr (combine (treeToOperand (evToTree d)) (treeToOperand (evToTree e))) = _
    rw [ihd hcd, ihe hce]
    rfl

/-- The object order as a `Bool` "strictly less" test on trees. -/
def ltT (x y : Tree) : Bool :=
  match Tree.cmp x y with
  | .lt => true
  | _ => false

theorem ltT_lt {x y : Tree} (h : ltT x y = true) : Tree.cmp x y = .lt := by
  unfold ltT at h
  cases hc : Tree.cmp x y with
  | lt => rfl
  | eq => rw [hc] at h; exact Bool.noConfusion h
  | gt => rw [hc] at h; exact Bool.noConfusion h

theorem ltT_of_lt {x y : Tree} (h : Tree.cmp x y = .lt) : ltT x y = true := by
  unfold ltT; rw [h]

/-- Object canonicity: a tree is canonical iff every node is sorted-strict
(the F-obj counterpart of `canon`; `Tree.pairing` always produces such a
tree from distinct canonical children). -/
def canonB : Tree → Bool
  | .a => true
  | .b => true
  | .node x y => canonB x && canonB y && ltT x y

/-- **Round-trip obj → F-ev → obj**: every canonical tree is recovered
from its operand translation. -/
theorem opToTree_treeToOperand : ∀ t : Tree, canonB t = true → opToTree (treeToOperand t) = t := by
  intro t
  induction t with
  | a => intro _; rfl
  | b => intro _; rfl
  | node x y ihx ihy =>
    intro hc
    have hs := band_split hc
    have hcx : canonB x = true := (band_split hs.1).1
    have hcy : canonB y = true := (band_split hs.1).2
    have hlt : Tree.cmp x y = .lt := ltT_lt hs.2
    show opToTree (Sum.inr (combine (treeToOperand x) (treeToOperand y))) = _
    show evToTree (combine (treeToOperand x) (treeToOperand y)) = _
    rw [evToTree_combine, ihx hcx, ihy hcy, Tree.pairing_of_lt hlt]

/-! ## 7. Faithfulness, image, and "a distinction is never an atom" -/

/-- **Faithfulness** (`evToTree` injective on `D`): distinct canonical
distinctions have distinct trees — structure preservation. -/
theorem evToTree_injective {d e : Ev} (hcd : canon d = true) (hce : canon e = true)
    (h : evToTree d = evToTree e) : d = e := by
  have hd := treeToOperand_evToTree d hcd
  have he := treeToOperand_evToTree e hce
  rw [h] at hd
  have : Sum.inr d = (Sum.inr e : Pole ⊕ Ev) := hd.symm.trans he
  exact Sum.inr.inj this

/-- Contrapositive: distinct canonical distinctions stay distinct after
translation. -/
theorem evToTree_ne {d e : Ev} (hcd : canon d = true) (hce : canon e = true)
    (h : d ≠ e) : evToTree d ≠ evToTree e :=
  fun heq => h (evToTree_injective hcd hce heq)

/-- A distinction's tree is never an atom (§4.4): the reified difference is
genuinely a new something. -/
theorem evToTree_composite (e : Ev) : evToTree e ≠ Tree.a ∧ evToTree e ≠ Tree.b := by
  obtain ⟨x, y, he⟩ := evToTree_node e
  rw [he]
  exact ⟨fun h => Tree.noConfusion h, fun h => Tree.noConfusion h⟩

/-- **Image characterization**: `evToTree` lands in canonical trees.  With
the round-trips this makes `evToTree : D ≅ {canonical composites}`. -/
theorem evToTree_canonB : ∀ e : Ev, canon e = true → canonB (evToTree e) = true := by
  intro e
  induction e with
  | pp p q =>
    intro hc
    have hs := band_split hc
    have hp : p = .l := Pole.eq_of_beq hs.1
    have hq : q = .r := Pole.eq_of_beq hs.2
    subst hp; subst hq
    rfl
  | pe p e ih =>
    intro hc
    have hce : canon e = true := hc
    rw [evToTree_pe]
    show (canonB (poleToTree p) && canonB (evToTree e) && ltT (poleToTree p) (evToTree e)) = true
    refine band_join (band_join ?_ (ih hce)) ?_
    · cases p <;> rfl
    · exact ltT_of_lt (cmp_pole_ev p e)
  | ee d e ihd ihe =>
    intro hc
    have hs := band_split hc
    have hs' := band_split hs.1
    have hcd : canon d = true := hs'.1
    have hce : canon e = true := hs'.2
    have hlt : Tree.cmp (evToTree d) (evToTree e) = .lt := ltEv_lt hs.2
    show canonB (Tree.pairing (evToTree d) (evToTree e)) = true
    rw [Tree.pairing_of_lt hlt]
    show (canonB (evToTree d) && canonB (evToTree e) && ltT (evToTree d) (evToTree e)) = true
    exact band_join (band_join (ihd hcd) (ihe hce)) (ltT_of_lt hlt)

/-! ## 8. The primordial element (R3 as a theorem) and the F-obj non-analogue -/

/-- Subterm relation on `Ev`. -/
inductive SubEv : Ev → Ev → Prop where
  | refl (e : Ev) : SubEv e e
  | pe {x : Ev} (p : Pole) {e : Ev} : SubEv x e → SubEv x (Ev.pe p e)
  | eeL {x : Ev} {d e : Ev} : SubEv x d → SubEv x (Ev.ee d e)
  | eeR {x : Ev} {d e : Ev} : SubEv x e → SubEv x (Ev.ee d e)

/-- **`prim_subterm`** (R3 as a theorem): every canonical distinction
contains the primordial distinction `prim = pp l r` as a subterm — every
distinction unfolds from the first distinction. -/
theorem prim_subterm : ∀ e : Ev, canon e = true → SubEv (Ev.pp .l .r) e := by
  intro e
  induction e with
  | pp p q =>
    intro hc
    have hs := band_split hc
    have hp : p = .l := Pole.eq_of_beq hs.1
    have hq : q = .r := Pole.eq_of_beq hs.2
    subst hp; subst hq
    exact SubEv.refl _
  | pe p e ih =>
    intro hc
    exact SubEv.pe p (ih hc)
  | ee d e ihd _ =>
    intro hc
    have hcd : canon d = true := (band_split (band_split hc).1).1
    exact SubEv.eeL (ihd hcd)

/-- The carrier-level version: `prim` is a subterm of every element of `D`. -/
theorem prim_subterm_D (d : D) : SubEv D.prim.val d.val :=
  prim_subterm d.val d.property

/-! ### The F-obj non-analogue — the event-primacy asymmetry (A1) -/

/-- Subterm relation on `Tree` (for the asymmetry statement). -/
inductive SubTree : Tree → Tree → Prop where
  | refl (t : Tree) : SubTree t t
  | nodeL {x l r : Tree} : SubTree x l → SubTree x (Tree.node l r)
  | nodeR {x l r : Tree} : SubTree x r → SubTree x (Tree.node l r)

/-- **No universal atom** (the F-obj non-analogue of `prim_subterm`): in
F-obj there is NO single object below every tree — the two atoms are
subterm-incomparable, so neither is a common lower element.  Contrast
`prim_subterm`: F-ev *does* have a least distinction.  This is the
event-primacy asymmetry A1: relocating the primordial two-ness below the
carrier gives F-ev a genuine bottom that F-obj lacks. -/
theorem no_universal_atom :
    ¬ SubTree Tree.a Tree.b ∧ ¬ SubTree Tree.b Tree.a := by
  refine ⟨?_, ?_⟩
  · intro h; cases h
  · intro h; cases h

end FEv

end Rederive
