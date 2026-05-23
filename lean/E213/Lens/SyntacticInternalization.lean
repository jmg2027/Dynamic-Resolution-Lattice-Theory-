import E213.Theory.Raw.API
import E213.Lens.Number.Nat213.Raw
import E213.Meta.Tactic.List213

/-!
# Lens.SyntacticInternalization — meta-syntax glyphs as Raws (§9.4 prototype)

Per `seed/AXIOM/06_lens_readings.md` §6.4 and
`research-notes/2026-05-18_lens_emergence_path.md` §2.7.

  - **L2**: 7-glyph alphabet, each glyph → a distinct Raw; the
    meta-meta-… cascade halts at L2.
  - **L3**: Polish-prefix printer + fuel-bounded parser + the
    universal round-trip theorem
    `∀ t, parseTree (printTree t) = some t`.
  - **L4 (this session,)**: reverse direction —
    `parseTree gs = some t → printTree t = gs` (lossless parser)
    + `printTree` injectivity.  Together with L3 these close the
    full bijection between `Tree` and `Range(printTree)`.

∅-axiom standard; all Nat arithmetic via Lean 4 core lemmas (no
`omega`, no `Nat.le_max_*`, no `Nat.sub_add_cancel`).
-/

namespace E213.Lens.SyntacticInternalization

open E213.Theory

/-! ### The 7-glyph alphabet -/

inductive Glyph
  | a
  | b
  | slash
  | lparen
  | rparen
  | comma
  | space
  deriving DecidableEq, Repr

/-! ### Glyph → Raw encoding -/

def Glyph.toRaw : Glyph → Raw
  | .a       => E213.Lens.Number.Nat213.Raw.numeral 0
  | .b       => E213.Lens.Number.Nat213.Raw.numeral 1
  | .slash   => E213.Lens.Number.Nat213.Raw.numeral 2
  | .lparen  => E213.Lens.Number.Nat213.Raw.numeral 3
  | .rparen  => E213.Lens.Number.Nat213.Raw.numeral 4
  | .comma   => E213.Lens.Number.Nat213.Raw.numeral 5
  | .space   => E213.Lens.Number.Nat213.Raw.numeral 6

theorem Glyph.toRaw_injective {g₁ g₂ : Glyph}
    (h : g₁.toRaw = g₂.toRaw) : g₁ = g₂ := by
  cases g₁ <;> cases g₂ <;>
    first | rfl | (exfalso; revert h; decide)

theorem Glyph.toRaw_injective' :
    ∀ {g₁ g₂ : Glyph}, g₁.toRaw = g₂.toRaw → g₁ = g₂ :=
  @Glyph.toRaw_injective

theorem Glyph.has_raw_image (g : Glyph) : ∃ r : Raw, r = g.toRaw :=
  ⟨g.toRaw, rfl⟩

/-! ### Polish-prefix printer -/

open E213.Term.Internal (Tree)

def printTree : Tree → List Glyph
  | .a         => [.a]
  | .b         => [.b]
  | .slash x y => .slash :: printTree x ++ printTree y

/-- The three computational cases of `printTree` are
    definitional (`rfl`) — `printTree .a = [.a]`, `printTree .b
    = [.b]`, and `printTree (.slash x y) = .slash :: printTree
    x ++ printTree y`.  No standalone lemmas needed; callers
    `unfold printTree`. -/
def printRaw (r : Raw) : List Glyph := printTree r.val

example :
    printRaw (Raw.slash Raw.a Raw.b (by decide))
      = [.slash, .a, .b] := by decide

example :
    printRaw (Raw.slash Raw.b Raw.a (by decide))
      = [.slash, .a, .b] := by decide

/-! ### Polish-prefix parser (fuel-bounded) -/

def parseHelper : Nat → List Glyph → Option (Tree × List Glyph)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, .a :: rest => some (.a, rest)
  | _ + 1, .b :: rest => some (.b, rest)
  | n + 1, .slash :: rest =>
      match parseHelper n rest with
      | none => none
      | some (x, rest1) =>
          match parseHelper n rest1 with
          | none => none
          | some (y, rest2) => some (.slash x y, rest2)
  | _ + 1, _ :: _ => none

def parseTree (gs : List Glyph) : Option Tree :=
  match parseHelper gs.length gs with
  | some (t, []) => some t
  | _ => none

example : parseTree (printTree .a) = some .a := by decide
example : parseTree (printTree .b) = some .b := by decide
example : parseTree (printTree (.slash .a .b)) = some (.slash .a .b) := by
  decide
example :
    parseTree (printTree (.slash .b (.slash .a .b)))
      = some (.slash .b (.slash .a .b)) := by decide

/-! ### Slash unfolding helper -/

theorem parseHelper_slash_succ (n : Nat) (rest : List Glyph) :
    parseHelper (n + 1) (.slash :: rest)
      = (match parseHelper n rest with
         | none => none
         | some (x, rest1) =>
             match parseHelper n rest1 with
             | none => none
             | some (y, rest2) => some (Tree.slash x y, rest2)) := rfl

/-! ### Universal L3 round-trip

Uses `E213.Tactic.List213.{append_nil, append_assoc,
length_append}` — propext-free replacements for the Lean 4 core
list lemmas (which carry `propext`). -/

open E213.Tactic.List213 (append_nil append_assoc length_append)

def treeSize : Tree → Nat
  | .a         => 1
  | .b         => 1
  | .slash x y => 1 + treeSize x + treeSize y

theorem parseHelper_fuel_succ :
    ∀ (n : Nat) (gs : List Glyph) (res : Tree × List Glyph),
      parseHelper n gs = some res
        → parseHelper (n + 1) gs = some res := by
  intro n
  induction n with
  | zero =>
      intro gs res h
      exact Option.noConfusion h
  | succ k ih =>
      intro gs res h
      cases gs with
      | nil => exact Option.noConfusion h
      | cons g rest =>
          cases g with
          | a => exact h
          | b => exact h
          | slash =>
              show parseHelper (k + 2) (.slash :: rest) = some res
              cases hk_eq : parseHelper k rest with
              | none =>
                  have hnone : parseHelper (k + 1) (.slash :: rest) = none := by
                    rw [parseHelper_slash_succ, hk_eq]
                  rw [hnone] at h
                  exact Option.noConfusion h
              | some p =>
                  obtain ⟨x, rest1⟩ := p
                  cases hk1_eq : parseHelper k rest1 with
                  | none =>
                      have hnone :
                          parseHelper (k + 1) (.slash :: rest) = none := by
                        rw [parseHelper_slash_succ, hk_eq]
                        show (match parseHelper k rest1 with
                              | none => none
                              | some (y, rest2) =>
                                  some (Tree.slash x y, rest2)) = none
                        rw [hk1_eq]
                      rw [hnone] at h
                      exact Option.noConfusion h
                  | some p2 =>
                      obtain ⟨y, rest2⟩ := p2
                      have h_val :
                          parseHelper (k + 1) (.slash :: rest)
                            = some (Tree.slash x y, rest2) := by
                        rw [parseHelper_slash_succ, hk_eq]
                        show (match parseHelper k rest1 with
                              | none => none
                              | some (y', rest2') =>
                                  some (Tree.slash x y', rest2'))
                            = some (Tree.slash x y, rest2)
                        rw [hk1_eq]
                      have hres : res = (Tree.slash x y, rest2) := by
                        rw [h_val] at h; exact (Option.some.inj h).symm
                      have hk' :
                          parseHelper (k + 1) rest = some (x, rest1) :=
                        ih _ _ hk_eq
                      have hk1' :
                          parseHelper (k + 1) rest1 = some (y, rest2) :=
                        ih _ _ hk1_eq
                      rw [hres, parseHelper_slash_succ, hk']
                      show (match parseHelper (k + 1) rest1 with
                            | none => none
                            | some (y', rest2') =>
                                some (Tree.slash x y', rest2'))
                          = some (Tree.slash x y, rest2)
                      rw [hk1']
          | lparen  => exact Option.noConfusion h
          | rparen  => exact Option.noConfusion h
          | comma   => exact Option.noConfusion h
          | space   => exact Option.noConfusion h

theorem parseHelper_fuel_mono (m k : Nat) (gs : List Glyph)
    (res : Tree × List Glyph) (h : parseHelper m gs = some res) :
    parseHelper (m + k) gs = some res := by
  induction k with
  | zero => exact h
  | succ j ih => exact parseHelper_fuel_succ _ _ _ ih

theorem parseHelper_printTree_append (t : Tree) :
    ∀ (rest : List Glyph),
      parseHelper (treeSize t) (printTree t ++ rest) = some (t, rest) := by
  induction t with
  | a => intro rest; rfl
  | b => intro rest; rfl
  | slash x y ihx ihy =>
      intro rest
      have hpat : 1 + treeSize x + treeSize y
                  = (treeSize x + treeSize y) + 1 := by
        rw [Nat.add_assoc 1 (treeSize x) (treeSize y),
            Nat.add_comm 1 (treeSize x + treeSize y)]
      have hx_lift :
          parseHelper (treeSize x + treeSize y)
                       (printTree x ++ (printTree y ++ rest))
            = some (x, printTree y ++ rest) :=
        parseHelper_fuel_mono (treeSize x) (treeSize y) _ _
          (ihx (printTree y ++ rest))
      have hy_lift :
          parseHelper (treeSize x + treeSize y) (printTree y ++ rest)
            = some (y, rest) := by
        rw [Nat.add_comm (treeSize x) (treeSize y)]
        exact parseHelper_fuel_mono (treeSize y) (treeSize x) _ _
          (ihy rest)
      show parseHelper (treeSize (Tree.slash x y))
              (printTree (Tree.slash x y) ++ rest)
          = some (Tree.slash x y, rest)
      show parseHelper (1 + treeSize x + treeSize y)
              (.slash :: printTree x ++ printTree y ++ rest)
          = some (Tree.slash x y, rest)
      rw [show (.slash :: printTree x ++ printTree y ++ rest : List Glyph)
            = .slash :: (printTree x ++ (printTree y ++ rest)) from
              congrArg (Glyph.slash :: ·)
                (append_assoc (printTree x) (printTree y) rest)]
      rw [hpat, parseHelper_slash_succ, hx_lift]
      show (match parseHelper (treeSize x + treeSize y)
                    (printTree y ++ rest) with
            | none => none
            | some (y', rest2') =>
                some (Tree.slash x y', rest2'))
          = some (Tree.slash x y, rest)
      rw [hy_lift]

theorem printTree_length_ge_size (t : Tree) :
    treeSize t ≤ (printTree t).length := by
  induction t with
  | a => exact Nat.le_refl _
  | b => exact Nat.le_refl _
  | slash x y ihx ihy =>
      show 1 + treeSize x + treeSize y
        ≤ (.slash :: (printTree x ++ printTree y)).length
      show 1 + treeSize x + treeSize y
        ≤ (printTree x ++ printTree y).length + 1
      rw [length_append]
      rw [show 1 + treeSize x + treeSize y
            = 1 + (treeSize x + treeSize y)
            from Nat.add_assoc 1 (treeSize x) (treeSize y)]
      rw [show (printTree x).length + (printTree y).length + 1
            = 1 + ((printTree x).length + (printTree y).length)
            from Nat.add_comm _ 1]
      exact Nat.add_le_add_left (Nat.add_le_add ihx ihy) 1

/-- **Universal round-trip**: `parseTree (printTree t) = some t`. -/
theorem parseTree_printTree (t : Tree) :
    parseTree (printTree t) = some t := by
  have hcorrect :
      parseHelper (treeSize t) (printTree t) = some (t, []) := by
    have := parseHelper_printTree_append t []
    rw [append_nil (printTree t)] at this
    exact this
  have hlen : treeSize t ≤ (printTree t).length :=
    printTree_length_ge_size t
  obtain ⟨k, hk⟩ := Nat.le.dest hlen
  have hlift :
      parseHelper (treeSize t + k) (printTree t) = some (t, []) :=
    parseHelper_fuel_mono (treeSize t) k _ _ hcorrect
  show (match parseHelper (printTree t).length (printTree t) with
        | some (t', []) => some t'
        | _ => none) = some t
  rw [← hk, hlift]

theorem parseTree_printRaw (r : Raw) :
    parseTree (printRaw r) = some r.val := by
  show parseTree (printTree r.val) = some r.val
  exact parseTree_printTree r.val


open E213.Tactic.List213 (append_nil append_assoc)

/-! ### Reverse round-trip — `printTree` is a left inverse for `parseTree`

Together with `parseTree_printTree`, these close the bijection
between `Tree` and `Range(printTree)`.  `printTree` is injective
(any two trees with the same printed form are equal), and `parseTree`
is a left inverse on its image (any successful parse round-trips
back to its source glyph list). -/

/-- **Soundness of `parseHelper`**: if `parseHelper n gs = some
    (t, rest)`, then the consumed prefix is exactly `printTree t`. -/
theorem parseHelper_sound :
    ∀ (n : Nat) (gs : List Glyph) (t : Tree) (rest : List Glyph),
      parseHelper n gs = some (t, rest) → gs = printTree t ++ rest := by
  intro n
  induction n with
  | zero =>
      intro gs t rest h
      exact Option.noConfusion h
  | succ k ih =>
      intro gs t rest h
      cases gs with
      | nil => exact Option.noConfusion h
      | cons g rest0 =>
          cases g with
          | a =>
              have heq : (Tree.a, rest0) = (t, rest) := Option.some.inj h
              have ht : t = Tree.a := (Prod.mk.inj heq).1.symm
              have hr : rest = rest0 := (Prod.mk.inj heq).2.symm
              rw [ht, hr]; rfl
          | b =>
              have heq : (Tree.b, rest0) = (t, rest) := Option.some.inj h
              have ht : t = Tree.b := (Prod.mk.inj heq).1.symm
              have hr : rest = rest0 := (Prod.mk.inj heq).2.symm
              rw [ht, hr]; rfl
          | slash =>
              show .slash :: rest0 = printTree t ++ rest
              cases hk : parseHelper k rest0 with
              | none =>
                  have hnone : parseHelper (k+1) (.slash :: rest0) = none := by
                    rw [parseHelper_slash_succ, hk]
                  rw [hnone] at h
                  exact Option.noConfusion h
              | some p =>
                  obtain ⟨x, rest1⟩ := p
                  cases hk1 : parseHelper k rest1 with
                  | none =>
                      have hnone : parseHelper (k+1) (.slash :: rest0) = none := by
                        rw [parseHelper_slash_succ, hk]
                        show (match parseHelper k rest1 with
                              | none => none
                              | some (y, rest2) =>
                                  some (Tree.slash x y, rest2)) = none
                        rw [hk1]
                      rw [hnone] at h
                      exact Option.noConfusion h
                  | some p2 =>
                      obtain ⟨y, rest2⟩ := p2
                      have hh : parseHelper (k+1) (.slash :: rest0)
                              = some (Tree.slash x y, rest2) := by
                        rw [parseHelper_slash_succ, hk]
                        show (match parseHelper k rest1 with
                              | none => none
                              | some (y', rest2') =>
                                  some (Tree.slash x y', rest2'))
                            = some (Tree.slash x y, rest2)
                        rw [hk1]
                      rw [hh] at h
                      have heq : (Tree.slash x y, rest2) = (t, rest) :=
                        Option.some.inj h
                      have ht : t = Tree.slash x y := (Prod.mk.inj heq).1.symm
                      have hr : rest = rest2 := (Prod.mk.inj heq).2.symm
                      have ihx : rest0 = printTree x ++ rest1 := ih _ _ _ hk
                      have ihy : rest1 = printTree y ++ rest2 := ih _ _ _ hk1
                      rw [ht, hr]
                      show .slash :: rest0
                            = (.slash :: printTree x ++ printTree y) ++ rest2
                      rw [ihx, ihy]
                      show .slash :: (printTree x ++ (printTree y ++ rest2))
                            = (.slash :: printTree x ++ printTree y) ++ rest2
                      rw [← append_assoc (printTree x) (printTree y) rest2]
                      rfl
          | lparen => exact Option.noConfusion h
          | rparen => exact Option.noConfusion h
          | comma  => exact Option.noConfusion h
          | space  => exact Option.noConfusion h

/-- **Reverse round-trip**: if `parseTree gs = some t`, then
    `printTree t = gs`.  The "lossless parser" property. -/
theorem printTree_parseTree (gs : List Glyph) (t : Tree)
    (h : parseTree gs = some t) : printTree t = gs := by
  show printTree t = gs
  rw [show parseTree gs
        = (match parseHelper gs.length gs with
           | some (t', []) => some t'
           | _ => none) from rfl] at h
  cases hph : parseHelper gs.length gs with
  | none =>
      rw [hph] at h; exact Option.noConfusion h
  | some p =>
      obtain ⟨t', rest⟩ := p
      cases rest with
      | nil =>
          rw [hph] at h
          have ht : t' = t := Option.some.inj h
          have hsound : gs = printTree t' ++ [] :=
            parseHelper_sound _ _ _ _ hph
          rw [ht] at hsound
          rw [append_nil] at hsound
          exact hsound.symm
      | cons _ _ =>
          rw [hph] at h; exact Option.noConfusion h

/-- **printTree is injective**: any two trees with the same printed
    form are equal.  Trivial corollary of `parseTree_printTree`. -/
theorem printTree_injective {t₁ t₂ : Tree}
    (h : printTree t₁ = printTree t₂) : t₁ = t₂ := by
  have h1 : parseTree (printTree t₁) = some t₁ := parseTree_printTree t₁
  have h2 : parseTree (printTree t₂) = some t₂ := parseTree_printTree t₂
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- **Reverse round-trip for Raw**: dual of `parseTree_printRaw`. -/
theorem printRaw_parseTree (gs : List Glyph) (r : E213.Theory.Raw)
    (h : parseTree gs = some r.val) : printRaw r = gs :=
  printTree_parseTree gs r.val h

/-! ### Injectivity biconditionals (, iteration #14)

Companion biconditional forms of `printTree_injective` and the
lifted `printRaw` version.  Both follow trivially from injectivity
+ congrArg. -/

/-- `printTree` equality biconditional. -/
theorem printTree_eq_iff {t₁ t₂ : E213.Term.Internal.Tree} :
    printTree t₁ = printTree t₂ ↔ t₁ = t₂ :=
  ⟨printTree_injective, fun h => h ▸ rfl⟩

/-- `printRaw` injectivity — lifted from `printTree_injective`
    through `Subtype.ext`. -/
theorem printRaw_injective {r₁ r₂ : E213.Theory.Raw}
    (h : printRaw r₁ = printRaw r₂) : r₁ = r₂ := by
  have h' : printTree r₁.val = printTree r₂.val := h
  exact Subtype.ext (printTree_injective h')

/-- `printRaw` equality biconditional. -/
theorem printRaw_eq_iff {r₁ r₂ : E213.Theory.Raw} :
    printRaw r₁ = printRaw r₂ ↔ r₁ = r₂ :=
  ⟨printRaw_injective, fun h => h ▸ rfl⟩

end E213.Lens.SyntacticInternalization
