import E213.Theory.Raw.API

/-!
# Lens.Number.Nat213.Raw — canonical Method A chart on Raw

The canonical chart representative of ℕ₊ in `Raw`: starting from
`Raw.a` ("1") and stepping by `slashOrSelf · Raw.b`.  This file
contains only the *chart structure* — chart constructors
(`one`, `succ`, `numeral`) plus the projection
(`value : Raw → Nat`) and their atomic lemmas.

**Arithmetic on Raw is intentionally absent.** Per
`research-notes/2026-05-18_lens_emergence_path.md` §5 Option C: the
abstract number-theoretic operations (`+`, `·`) live on `Nat` (the
abstract object); the Raw side carries only the canonical
representative.  Closed-Raw arithmetic is a category error — Raw
is for *representing* numbers, `Nat` is for *being* them.

For arithmetic on the chain:
  - **Nat side**: do arithmetic on `Nat` directly, then map back
    via `Raw.numeral`.
  - **Raw-subtype side**: see `Lens.Number.Nat213.Chain`, where
    operations route through `Nat` and the Raw-subtype carrier is
    preserved as a *type* (not via closed-Raw computation).

Other related files in this directory:
  - `Peano.lean`  — separate inductive `Nat213` with its own
                    arithmetic; ergonomic parallel (not lens-derived).
  - `Bridge.lean` — Peano ↔ Raw chart bijection at the `value` level.
  - `Core.lean`   — `{n : Nat // 1 ≤ n}` Nat-subtype carrier.
  - `Chain.lean`  — `{r : Raw // IsMethodAChain r}` Raw-subtype
                    carrier with Nat-routed arithmetic.

**Framing (per `seed/AXIOM/09_chart_relativity.md`).**  This is *one
representation* along the lens-emergence path — Method A's chain
under `Lens.leaves`.  `Raw.a` and `Raw.b` are chart-local labels
(§9.1); under a different chart, any pair of distinct Raws could
serve as the chain seeds.  See also
`Lens.Number.Nat213.ChartGeneral` for the parameterised version.

∅-axiom standard; no Mathlib / Classical / propext / Quot.sound /
omega / native_decide.
-/

namespace E213.Lens.Number.Nat213.Raw

open E213.Theory E213.Theory.Raw.Endomorphic

/-! ### Chart constructors -/

/-- ℕ₊'s `1` — the Method A chain start; the minimum observation
    (a Raw with leaves = 1). -/
def one : Raw := Raw.a

/-- Successor — wraps `n` in `Raw.b` via `slashOrSelf`. -/
def succ (n : Raw) : Raw := slashOrSelf n Raw.b

/-- Enumeration `Nat → Raw` (off-by-one: `numeral n` corresponds to
    the (n+1)-th positive natural, i.e. value `n+1`). -/
def numeral : Nat → Raw
  | 0     => one
  | n + 1 => succ (numeral n)

theorem numeral_zero : numeral 0 = one := rfl

theorem numeral_succ (n : Nat) : numeral (n + 1) = succ (numeral n) := rfl

/-! ### Projection to `Nat` (= `Lens.leaves.view` for Raw) -/

/-- Leaves-count projection: `value r` is the number of atom leaves
    in the Raw tree.  Equal to `Lens.leaves.view r`. -/
def value (r : Raw) : Nat := Raw.fold 1 1 (· + ·) r

theorem value_one : value one = 1 := rfl
theorem value_a   : value Raw.a = 1 := rfl
theorem value_b   : value Raw.b = 1 := rfl

/-- The successor wrap adds one leaf, provided the wrapped element
    is not literally `Raw.b` (otherwise `slashOrSelf` collapses). -/
theorem value_succ_of_ne (n : Raw) (h : n ≠ Raw.b) :
    value (succ n) = value n + 1 := by
  unfold succ value
  rw [slashOrSelf_of_ne h]
  show Raw.fold 1 1 (· + ·) (Raw.slash n Raw.b h) = _
  rw [Raw.fold_slash 1 1 (· + ·) (fun u v => Nat.add_comm u v) n Raw.b h]
  show Raw.fold 1 1 (· + ·) n + Raw.fold 1 1 (· + ·) Raw.b
     = Raw.fold 1 1 (· + ·) n + 1
  rfl

/-! ### Chain invariant -/

/-- Every `Raw.numeral n` differs from `Raw.b` — Method A chain
    structural invariant.  Enables `value_succ_of_ne` on numerals
    and is the chain-element-≠-Raw.b lemma. -/
theorem numeral_ne_b (n : Nat) : numeral n ≠ Raw.b := by
  induction n with
  | zero =>
      intro h
      exact Term.Internal.Tree.noConfusion (congrArg Subtype.val h)
  | succ k ih =>
      show succ (numeral k) ≠ Raw.b
      unfold succ slashOrSelf
      rw [dif_neg ih]
      intro h
      have hval : (Raw.slash (numeral k) Raw.b ih).val = Raw.b.val :=
        congrArg Subtype.val h
      unfold Raw.slash at hval
      split at hval
      · exact Term.Internal.Tree.noConfusion hval
      · exact Term.Internal.Tree.noConfusion hval
      · rename_i hcmp
        exact ih (Subtype.ext (Term.Internal.Tree.cmp_eq_to_eq _ _ hcmp))

/-! ### Value on numerals -/

/-- `value (numeral n) = n + 1` — Method A off-by-one. -/
theorem value_numeral (n : Nat) : value (numeral n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show value (succ (numeral k)) = (k + 1) + 1
      rw [value_succ_of_ne _ (numeral_ne_b k), ih]

/-- `numeral` is injective: distinct Nat indices produce distinct
    chain Raws.  Proof via `value`: `value (numeral n) = n + 1` and
    `value` is constant on the LHS-RHS image. -/
theorem numeral_injective {m n : Nat} (h : numeral m = numeral n) : m = n := by
  have hv : value (numeral m) = value (numeral n) := congrArg value h
  rw [value_numeral, value_numeral] at hv
  exact Nat.succ.inj hv

/-! ### Surjectivity of `value` onto ℕ₊ (added 2026-05-18)

Together with `numeral_injective`, this establishes that
`Range(value) = {n : Nat | 1 ≤ n} = ℕ₊` exactly.  The Method A
numerals provide a section `ℕ → Raw` that, restricted to
`{n | 0 ≤ n}`, hits each natural ≥ 1 via the off-by-one
`value (numeral n) = n + 1`. -/

/-- **Surjectivity of `value` onto ℕ₊**: for every `n ≥ 1`, the
    Method A numeral `numeral (n - 1)` is a Raw with `value = n`.
    This is the rigorous form of "ℕ₊ is the image of the leaves
    Lens" — combined with the trivial `1 ≤ value r` for any `r`,
    `Range(value)` is exactly `{n | 1 ≤ n}`. -/
theorem value_surjective_on_ge_one (n : Nat) (hn : 1 ≤ n) :
    ∃ r : Raw, value r = n := by
  refine ⟨numeral (n - 1), ?_⟩
  rw [value_numeral]
  -- goal: (n - 1) + 1 = n
  exact Nat.succ_pred_eq_of_pos hn

/-- The Method A numeral chain is a section of `value`: for every
    `n ≥ 1`, `value (numeral (n - 1)) = n`.  Constructive form of
    `value_surjective_on_ge_one`. -/
theorem value_numeral_pred (n : Nat) (hn : 1 ≤ n) :
    value (numeral (n - 1)) = n := by
  rw [value_numeral]
  exact Nat.succ_pred_eq_of_pos hn

end E213.Lens.Number.Nat213.Raw
