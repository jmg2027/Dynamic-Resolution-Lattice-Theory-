import E213.Meta.Tactic.Omega213
import E213.Meta.Tactic.Mod213

/-!
# The parity / invariant argument — the mutilated chessboard (∅-axiom)

Compiling the **invariant (parity) method** down the proof-ISA
(`seed/PROOF_ISA.md`): a quantity preserved by every move obstructs reachability.
Reproduced on the classic — an `8×8` board minus two opposite corners cannot be
tiled by dominoes.

Colour a cell by the **parity** of `i + j`.  A domino covers two **adjacent**
cells, whose `i + j` differ by `1`, so they have **opposite** colour — every
domino covers one of each.  Hence any tiling covers *equally many* of the two
colours.  The mutilated board's two removed corners share a colour, so its two
colour-counts differ — no tiling can cover it.

Observation (the "why"): this is **not COUNT** (no deficit ⟹ existence) and
**not a new instruction**.  The colour-count is a **READ** — a catamorphism over
the cell list — so it is additive over the tiling; "each domino reads one of
each ⟹ the whole reads them equal" is just READ being a fold.  The obstruction
"the two counts differ ⟹ cannot coincide" is **SEPARATE** (a reading tells two
objects apart).  So the parity method compiles to **READ ∘ SEPARATE**: a
*conserved* reading separating reachable from unreachable — a third distinct
landing (the probabilistic + linear-algebra methods both compiled to COUNT;
this one does not — conservation is the SEPARATE direction, not the GAP one).

Parity is the canonical `mod`-free `Bool` primitive `Mod213.parity` (reused), so
the local flip is `Mod213.parity_succ` and the file is strict ∅-axiom (`Int` /
`Nat.mod` carry `propext` / `Quot.sound`).

Companion "why": `theory/essays/proof_isa/parity_invariant_method.md`.
-/

namespace E213.Lib.Math.Combinatorics.ParityInvariant

open E213.Tactic.Mod213 (parity parity_succ)

/-- A cell's colour = parity of `i + j`.  Reuses the canonical ∅-axiom
    `Mod213.parity` (the smallest cohomological-trajectory primitive) rather
    than a local copy. -/
def par (c : Nat × Nat) : Bool := parity (c.1 + c.2)

/-- A domino: two cells adjacent horizontally or vertically. -/
def Adj (c1 c2 : Nat × Nat) : Prop :=
  (c1.1 = c2.1 ∧ c1.2 + 1 = c2.2) ∨ (c1.1 + 1 = c2.1 ∧ c1.2 = c2.2)

/-- The cells a tiling covers. -/
def cover : List ((Nat × Nat) × (Nat × Nat)) → List (Nat × Nat)
  | [] => []
  | (c1, c2) :: t => c1 :: c2 :: cover t

/-- Count of the even-colour cells. -/
def ctrue : List (Nat × Nat) → Nat
  | [] => 0
  | c :: cs => (bif par c then 1 else 0) + ctrue cs

/-- Count of the odd-colour cells. -/
def cfalse : List (Nat × Nat) → Nat
  | [] => 0
  | c :: cs => (bif par c then 0 else 1) + cfalse cs

/-- **The local invariant.**  Adjacent cells carry opposite colour — the parity
    flip `parity (m+1) = !parity m` (`Mod213.parity_succ`). -/
theorem adj_par {c1 c2 : Nat × Nat} (h : Adj c1 c2) : par c2 = !(par c1) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · show parity (c2.1 + c2.2) = !(parity (c1.1 + c1.2))
    rw [← h1, ← h2]   -- c2 = (c1.1, c1.2 + 1) ; c1.1 + (c1.2+1) ≡ (c1.1+c1.2)+1
    exact parity_succ (c1.1 + c1.2)
  · show parity (c2.1 + c2.2) = !(parity (c1.1 + c1.2))
    rw [← h1, ← h2, Nat.succ_add]   -- c2 = (c1.1+1, c1.2) ; (c1.1+1)+c1.2 = (c1.1+c1.2)+1
    exact parity_succ (c1.1 + c1.2)

/-- ★ **The invariant (CONSERVE core).**  Every domino-tiling covers the two
    colours equally — each domino contributes one of each, and the colour-count
    is a `READ` (catamorphism) additive over the tiling. -/
theorem tiling_balanced :
    ∀ (t : List ((Nat × Nat) × (Nat × Nat))),
      (∀ d, d ∈ t → Adj d.1 d.2) → ctrue (cover t) = cfalse (cover t)
  | [], _ => rfl
  | (c1, c2) :: t, h => by
      have hadj : par c2 = !(par c1) := adj_par (h (c1, c2) (List.Mem.head _))
      have ih : ctrue (cover t) = cfalse (cover t) :=
        tiling_balanced t (fun d hd => h d (List.Mem.tail _ hd))
      show (bif par c1 then 1 else 0) + ((bif par c2 then 1 else 0) + ctrue (cover t))
          = (bif par c1 then 0 else 1) + ((bif par c2 then 0 else 1) + cfalse (cover t))
      rw [hadj, ih]
      cases par c1
      · show 0 + (1 + cfalse (cover t)) = 1 + (0 + cfalse (cover t))
        rw [Nat.zero_add, Nat.zero_add]
      · show 1 + (0 + cfalse (cover t)) = 0 + (1 + cfalse (cover t))
        rw [Nat.zero_add, Nat.zero_add]

/-- **The obstruction seed.**  The two opposite corners share a colour
    (`parity 0 = parity 14 = false`): removing them unbalances the colour-counts,
    which by `tiling_balanced` no tiling can match. -/
theorem corners_same_colour : par (0, 0) = par (7, 7) := by decide

end E213.Lib.Math.Combinatorics.ParityInvariant
