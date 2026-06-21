import E213.Lib.Math.Combinatorics.Sperner
import E213.Lib.Math.Combinatorics.BinomialInversion
import E213.Meta.Int213.Core

/-!
# Incidence-Fubini — one carrier-general swap underlies both COUNT-duality and the inversion engine (∅-axiom)

The two incidence-algebra unifications of the corpus each bottom out in a Fubini swap on a
0/1 (or `ℤ`) incidence matrix, but over *different* carriers:

  · **COUNT-duality** (`Combinatorics/CountDuality`) — union bound `=` LYM — runs on
    `Sperner.sumOver`, a fold over **`Nat`**;
  · **the incidence-inversion engine** (`IncidenceInversion`) — binomial / Möbius / Stirling
    inversion — runs on `BinomialInversion.sumZ`, a fold over **`Int`**.

This file proves both are the *same* swap. `genSum` is the fold over an arbitrary carrier
`R` with `add`/`zero`; `genSwap` is the carrier-general Fubini (summed by rows `=` summed by
columns), proven once from `add`-commutativity/associativity/unit. The bridges
`sumOver_eq_genSum` (Nat) and `sumZ_eq_genSum` (Int, over the range list) identify the two
library folds with `genSum`, so the Nat double-count engine and the Int double-count engine
are the two carrier-specializations of `genSwap` (`incidence_fubini_one_engine`).

This is the synthesis of the two incidence unifications at their root — one Fubini, two
carriers — a proven shared engine (not a juxtaposition: both halves are literally `genSwap`).
-/

namespace E213.Lib.Math.Combinatorics.IncidenceFubini

/-! ## §1 — the carrier-general fold and its Fubini swap -/

/-- General fold-sum over a list, carrier `R` with a binary `add` and a `zero`. -/
def genSum {β R : Type _} (add : R → R → R) (zero : R) (f : β → R) : List β → R
  | [] => zero
  | a :: l => add (f a) (genSum add zero f l)

/-- Middle-four exchange `(a+b)+(c+d) = (a+c)+(b+d)`, from commutativity + associativity. -/
private theorem add4 {R : Type _} (add : R → R → R)
    (hcomm : ∀ a b, add a b = add b a)
    (hassoc : ∀ a b c, add (add a b) c = add a (add b c)) (a b c d : R) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [hassoc a b (add c d), ← hassoc b c d, hcomm b c, hassoc c b d, ← hassoc a c (add b d)]

/-- The all-`zero` function folds to `zero`. -/
theorem genSum_zero_fun {β R : Type _} (add : R → R → R) (zero : R)
    (hzl : ∀ a, add zero a = a) :
    ∀ (L : List β), genSum add zero (fun _ => zero) L = zero
  | [] => rfl
  | _ :: l => by
      show add zero (genSum add zero (fun _ => zero) l) = zero
      rw [genSum_zero_fun add zero hzl l]; exact hzl zero

/-- `genSum` is additive in the summand (bilinearity, one side). -/
theorem genSum_add {β R : Type _} (add : R → R → R) (zero : R)
    (hcomm : ∀ a b, add a b = add b a)
    (hassoc : ∀ a b c, add (add a b) c = add a (add b c))
    (hzl : ∀ a, add zero a = a) (f g : β → R) :
    ∀ (L : List β),
      genSum add zero (fun x => add (f x) (g x)) L
        = add (genSum add zero f L) (genSum add zero g L)
  | [] => (hzl zero).symm
  | a :: l => by
      show add (add (f a) (g a)) (genSum add zero (fun x => add (f x) (g x)) l)
         = add (add (f a) (genSum add zero f l)) (add (g a) (genSum add zero g l))
      rw [genSum_add add zero hcomm hassoc hzl f g l,
          add4 add hcomm hassoc (f a) (g a) (genSum add zero f l) (genSum add zero g l)]

/-- `genSum` distributes over `append` (associativity + unit). -/
theorem genSum_append {β R : Type _} (add : R → R → R) (zero : R)
    (hassoc : ∀ a b c, add (add a b) c = add a (add b c))
    (hzl : ∀ a, add zero a = a) (f : β → R) :
    ∀ (L1 L2 : List β),
      genSum add zero f (L1 ++ L2) = add (genSum add zero f L1) (genSum add zero f L2)
  | [], L2 => by
      show genSum add zero f L2 = add zero (genSum add zero f L2)
      rw [hzl]
  | a :: L1, L2 => by
      show add (f a) (genSum add zero f (L1 ++ L2))
         = add (add (f a) (genSum add zero f L1)) (genSum add zero f L2)
      rw [genSum_append add zero hassoc hzl f L1 L2,
          hassoc (f a) (genSum add zero f L1) (genSum add zero f L2)]

/-- ★★★ **Incidence-Fubini (the carrier-general swap).**  A `Bool`/`R` incidence matrix `g`,
    folded by rows (`Σ_A Σ_c`), equals it folded by columns (`Σ_c Σ_A`), for any carrier with
    a commutative-associative `add` and unit `zero`.  The single engine both COUNT-duality
    (carrier `Nat`) and the inversion engine (carrier `Int`) run on. -/
theorem genSwap {β γ R : Type _} (add : R → R → R) (zero : R)
    (hcomm : ∀ a b, add a b = add b a)
    (hassoc : ∀ a b c, add (add a b) c = add a (add b c))
    (hzl : ∀ a, add zero a = a) (g : β → γ → R) :
    ∀ (F : List β) (C : List γ),
      genSum add zero (fun A => genSum add zero (fun c => g A c) C) F
        = genSum add zero (fun c => genSum add zero (fun A => g A c) F) C
  | [], C => by
      show (zero : R) = genSum add zero (fun _ => zero) C
      rw [genSum_zero_fun add zero hzl C]
  | A :: F, C => by
      show add (genSum add zero (fun c => g A c) C)
              (genSum add zero (fun A' => genSum add zero (fun c => g A' c) C) F)
         = genSum add zero (fun c => add (g A c) (genSum add zero (fun A' => g A' c) F)) C
      rw [genSwap add zero hcomm hassoc hzl g F C]
      exact (genSum_add add zero hcomm hassoc hzl
        (fun c => g A c) (fun c => genSum add zero (fun A' => g A' c) F) C).symm

/-! ## §2 — bridges: the two library folds are `genSum` -/

/-- COUNT-duality's `Nat` fold is `genSum` at `(Nat.add, 0)`. -/
theorem sumOver_eq_genSum {β : Type _} (f : β → Nat) (L : List β) :
    Sperner.sumOver f L = genSum Nat.add 0 f L := by
  induction L with
  | nil => rfl
  | cons a l ih =>
      show Nat.add (f a) (Sperner.sumOver f l) = Nat.add (f a) (genSum Nat.add 0 f l)
      rw [ih]

/-- The range list `[0, 1, …, n−1]` — the index set of the `Int` range-fold. -/
def rangeL : Nat → List Nat
  | 0 => []
  | n + 1 => rangeL n ++ [n]

/-- The inversion engine's `Int` range-fold is `genSum` at `(Int.add, 0)` over `rangeL`. -/
theorem sumZ_eq_genSum (f : Nat → Int) :
    ∀ n, BinomialInversion.sumZ n f = genSum Int.add (0 : Int) f (rangeL n)
  | 0 => rfl
  | n + 1 => by
      have hz0 : ∀ a : Int, a + 0 = a :=
        fun a => (E213.Meta.Int213.add_comm a 0).trans (E213.Meta.Int213.zero_add a)
      show BinomialInversion.sumZ n f + f n = genSum Int.add (0 : Int) f (rangeL n ++ [n])
      rw [genSum_append Int.add (0 : Int) E213.Meta.Int213.add_assoc E213.Meta.Int213.zero_add
            f (rangeL n) [n],
          sumZ_eq_genSum f n]
      show Int.add (genSum Int.add (0 : Int) f (rangeL n)) (f n)
         = Int.add (genSum Int.add (0 : Int) f (rangeL n)) (f n + 0)
      rw [hz0]

/-! ## §3 — the capstone: one engine, two carriers -/

/-- ★★★ **One Fubini engine, two carriers.**  The double-count swap used by COUNT-duality
    (carrier `Nat`, `Sperner.sumOver`, via `sumOver_eq_genSum`) and the swap used by the
    incidence-inversion engine (carrier `Int`, `BinomialInversion.sumZ`, via `sumZ_eq_genSum`)
    are the two carrier-specializations of the single `genSwap`.  The two incidence-algebra
    unifications of the corpus share one root. -/
theorem incidence_fubini_one_engine :
    (∀ {β γ : Type} (g : β → γ → Nat) (F : List β) (C : List γ),
        genSum Nat.add 0 (fun A => genSum Nat.add 0 (fun c => g A c) C) F
          = genSum Nat.add 0 (fun c => genSum Nat.add 0 (fun A => g A c) F) C)
    ∧ (∀ {β γ : Type} (g : β → γ → Int) (F : List β) (C : List γ),
        genSum Int.add (0 : Int) (fun A => genSum Int.add (0 : Int) (fun c => g A c) C) F
          = genSum Int.add (0 : Int) (fun c => genSum Int.add (0 : Int) (fun A => g A c) F) C) :=
  ⟨fun g F C => genSwap Nat.add 0 Nat.add_comm Nat.add_assoc Nat.zero_add g F C,
   fun g F C => genSwap Int.add (0 : Int)
     E213.Meta.Int213.add_comm E213.Meta.Int213.add_assoc E213.Meta.Int213.zero_add g F C⟩

end E213.Lib.Math.Combinatorics.IncidenceFubini
