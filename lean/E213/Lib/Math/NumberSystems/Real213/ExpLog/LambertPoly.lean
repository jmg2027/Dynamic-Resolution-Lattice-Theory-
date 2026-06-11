import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut
import E213.Meta.Nat.PolyNatMTactic

/-!
# LambertPoly — the constant-first polynomial layer (the weld's connection infra)

`LowerBase`'s last layer is per-`q²`-grade: the product `devA·s_J` must be
compared with `(2J+1)·devB·c_J` **coefficientwise** (every evaluated shortcut
fails at the margins — the per-grade cancellation is the content).  This file
provides the grading infrastructure:

  * `evc` — constant-first evaluation `evc q (c :: cs) = c + q²·evc q cs`
    (position = `q²`-power).  Unlike `dev` (head = highest power), **no length
    conditions appear anywhere**: `evc_ladd` is unconditional, and the polynomial
    product is the standard recursion `lmulC (a :: as) b = ladd (lsmul a b)
    (0 :: lmulC as b)` with `evc_lmulC : evc (lmulC a b) = evc a · evc b`.
  * `rev` + `dev_eq_evc_rev` — the bridge to the weld's `dev`-world:
    `dev q l = evc q (rev l)`, so `dev q (AP n)` enters the graded layer as
    `evc q (rev (AP n))`.
  * `cListC/sListC` — the coefficient lists of the cleared cosh/sinh partials
    (`evc_cListC : evc q (cListC J) = coshNum q J`, likewise sinh).
  * the **connection statements** (`conn_A`, `conn_B`): the two sides of the
    `LowerBase` cross are `evc`s of explicit convolutions —
    `devA·s_J = evc (lmulC (rev (AP (2i+1))) (sListC J))` and
    `(2J+1)·devB·c_J = evc (lmulC (rev (BP (2i+1))) (lsmul (2J+1) (cListC J)))`.

What remains after this file: the per-coefficient comparison of the two
convolutions through the master identity (`LambertMasterId`) + halving — the
coefficient recursion `nth (lmulC (a :: as) b) (p+1) = a·nth b (p+1) +
nth (lmulC as b) p` needs no closed convolution formula.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
  (ladd lsmul AP BP dev dev_cons coshNum sinhNum)

/-! ## §1 — constant-first evaluation -/

/-- Constant-first evaluation at `q²`: position = power.  The dual of `dev`. -/
def evc (q : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => c + q ^ 2 * evc q cs

/-- `evc` is additive over `ladd` — **no length condition** (the tail padding is
    on the high-power side, which `evc` reads correctly). -/
theorem evc_ladd (q : Nat) : ∀ (a b : List Nat),
    evc q (ladd a b) = evc q a + evc q b
  | [], b => (Nat.zero_add (evc q b)).symm
  | _ :: _, [] => (Nat.add_zero _).symm
  | a :: as, b :: bs => by
    show (a + b) + q ^ 2 * evc q (ladd as bs) = (a + q ^ 2 * evc q as) + (b + q ^ 2 * evc q bs)
    rw [evc_ladd q as bs]
    ring_nat

theorem evc_lsmul (q k : Nat) : ∀ l : List Nat, evc q (lsmul k l) = k * evc q l
  | [] => (Nat.mul_zero k).symm
  | c :: cs => by
    show k * c + q ^ 2 * evc q (lsmul k cs) = k * (c + q ^ 2 * evc q cs)
    rw [evc_lsmul q k cs]
    ring_nat

theorem evc_shift (q : Nat) (l : List Nat) : evc q (0 :: l) = q ^ 2 * evc q l := by
  show 0 + q ^ 2 * evc q l = q ^ 2 * evc q l
  rw [Nat.zero_add]

/-! ## §2 — the polynomial product -/

/-- Constant-first polynomial product: the standard convolution recursion. -/
def lmulC : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: as, b => ladd (lsmul a b) (0 :: lmulC as b)

/-- ★★★ **`evc` is multiplicative**: `evc (lmulC a b) = evc a · evc b` —
    two-line induction thanks to the unconditional `evc_ladd`. -/
theorem evc_lmulC (q : Nat) : ∀ (a b : List Nat),
    evc q (lmulC a b) = evc q a * evc q b
  | [], b => by
    show (0 : Nat) = 0 * evc q b
    rw [Nat.zero_mul]
  | a :: as, b => by
    show evc q (ladd (lsmul a b) (0 :: lmulC as b)) = (a + q ^ 2 * evc q as) * evc q b
    rw [evc_ladd, evc_lsmul, evc_shift, evc_lmulC q as b]
    ring_nat

/-! ## §3 — the reversal bridge to `dev` -/

/-- List reversal (own recursion, defeq-controlled). -/
def rev : List Nat → List Nat
  | [] => []
  | c :: cs => rev cs ++ [c]

theorem len_app_single : ∀ (l : List Nat) (c : Nat), (l ++ [c]).length = l.length + 1
  | [], _ => rfl
  | _ :: cs, c => congrArg (· + 1) (len_app_single cs c)

theorem len_rev : ∀ l : List Nat, (rev l).length = l.length
  | [] => rfl
  | c :: cs => by
    show (rev cs ++ [c]).length = cs.length + 1
    rw [len_app_single (rev cs) c, len_rev cs]

/-- Appending a constant adds it at the top power. -/
theorem evc_append_single (q : Nat) : ∀ (l : List Nat) (c : Nat),
    evc q (l ++ [c]) = evc q l + c * q ^ (2 * l.length)
  | [], c => by
    show c + q ^ 2 * 0 = 0 + c * q ^ (2 * 0)
    rw [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    show c = c * q ^ 0
    rw [Nat.pow_zero, Nat.mul_one]
  | x :: xs, c => by
    show x + q ^ 2 * evc q (xs ++ [c])
        = (x + q ^ 2 * evc q xs) + c * q ^ (2 * (xs.length + 1))
    rw [evc_append_single q xs c,
        show q ^ (2 * (xs.length + 1)) = q ^ (2 * xs.length) * (q * q) from by
          show q ^ (2 * xs.length + 2) = q ^ (2 * xs.length) * (q * q)
          rw [Nat.pow_succ, Nat.pow_succ]; ring_nat,
        show (q : Nat) ^ 2 = q * q from by rw [Nat.pow_succ, Nat.pow_one]]
    ring_nat

/-- ★★★ **The bridge**: `dev q l = evc q (rev l)` — the weld's head-first world
    enters the constant-first graded layer. -/
theorem dev_eq_evc_rev (q : Nat) : ∀ l : List Nat, dev q l = evc q (rev l)
  | [] => rfl
  | c :: cs => by
    rw [dev_cons q c cs,
        show rev (c :: cs) = rev cs ++ [c] from rfl,
        evc_append_single q (rev cs) c, len_rev cs, dev_eq_evc_rev q cs,
        Nat.add_comm (evc q (rev cs)) (c * q ^ (2 * cs.length))]

/-! ## §4 — the cosh/sinh coefficient lists -/

/-- Constant-first coefficient list of `coshNum q J` (`q`-free!):
    `cListC (J+1) = 1 :: (2J+1)(2J+2)·cListC J`. -/
def cListC : Nat → List Nat
  | 0 => [1]
  | J + 1 => 1 :: lsmul ((2 * J + 1) * (2 * J + 2)) (cListC J)

/-- Constant-first coefficient list of `sinhNum q J`. -/
def sListC : Nat → List Nat
  | 0 => [1]
  | J + 1 => 1 :: lsmul ((2 * J + 2) * (2 * J + 3)) (sListC J)

theorem evc_cListC (q : Nat) : ∀ J, evc q (cListC J) = coshNum q J
  | 0 => by
    show 1 + q ^ 2 * 0 = 1
    rw [Nat.mul_zero]
  | J + 1 => by
    show 1 + q ^ 2 * evc q (lsmul ((2 * J + 1) * (2 * J + 2)) (cListC J))
        = (2 * J + 1) * (2 * J + 2) * q ^ 2 * coshNum q J + 1
    rw [evc_lsmul, evc_cListC q J]
    ring_nat

theorem evc_sListC (q : Nat) : ∀ J, evc q (sListC J) = sinhNum q J
  | 0 => by
    show 1 + q ^ 2 * 0 = 1
    rw [Nat.mul_zero]
  | J + 1 => by
    show 1 + q ^ 2 * evc q (lsmul ((2 * J + 2) * (2 * J + 3)) (sListC J))
        = (2 * J + 2) * (2 * J + 3) * q ^ 2 * sinhNum q J + 1
    rw [evc_lsmul, evc_sListC q J]
    ring_nat

/-! ## §5 — the connection: both `LowerBase` sides are `evc`s of convolutions -/

/-- ★★★★ The `A`-side of the `LowerBase` cross as a graded object:
    `dev (AP (2i+1)) · sinhNum q J = evc (lmulC (rev (AP (2i+1))) (sListC J))`. -/
theorem conn_A (q n J : Nat) :
    dev q (AP n) * sinhNum q J = evc q (lmulC (rev (AP n)) (sListC J)) := by
  rw [evc_lmulC, ← dev_eq_evc_rev, evc_sListC]

/-- ★★★★ The `B`-side:
    `(2J+1) · dev (BP (2i+1)) · coshNum q J
       = evc (lmulC (rev (BP (2i+1))) (lsmul (2J+1) (cListC J)))`. -/
theorem conn_B (q n J : Nat) :
    (2 * J + 1) * dev q (BP n) * coshNum q J
      = evc q (lmulC (rev (BP n)) (lsmul (2 * J + 1) (cListC J))) := by
  rw [evc_lmulC, ← dev_eq_evc_rev, evc_lsmul, evc_cListC]
  ring_nat

/-- Anchors: the graded layer reproduces the evaluated world (`q = 2`, `i = 1`,
    `J = 3`), and the two `LowerBase` sides match their convolutions. -/
theorem anchors :
    evc 2 (lmulC (rev (AP 3)) (sListC 3)) = dev 2 (AP 3) * sinhNum 2 3
    ∧ evc 2 (lmulC (rev (BP 3)) (lsmul 7 (cListC 3))) = 7 * dev 2 (BP 3) * coshNum 2 3
    ∧ rev (AP 3) = [6, 15] ∧ cListC 2 = [1, 12, 24] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## §6 — suffix dominance: coefficientwise Abel-carrying for `q ≥ 1`

The endgame's assembly weapon.  `evc 1` of a suffix (`List.drop k`) is the
suffix coefficient-sum; if every suffix sum of `a` is dominated by `b`'s
(equal lengths), then `evc q a ≤ evc q b` for every `q ≥ 1` — the Abel
transfer, proven as a joint ℕ-induction carrying the cross-statement
`evc q a + evc 1 b ≤ evc q b + evc 1 a` (whose cons-step cancels the heads). -/

open E213.Meta.Nat.NatRing213 (nat_add_right_cancel)

/-- Suffix dominance: every suffix coefficient-sum of `a` is at most `b`'s. -/
def SuffDom (a b : List Nat) : Prop :=
  ∀ k, evc 1 (List.drop k a) ≤ evc 1 (List.drop k b)

private theorem le_cancel_right {a b c : Nat} (h : a + c ≤ b + c) : a ≤ b := by
  have h2 : c + a ≤ c + b := by
    rw [Nat.add_comm c a, Nat.add_comm c b]; exact h
  exact E213.Tactic.NatHelper.le_of_add_le_add_left h2

/-- ★★★★ **The Abel transfer** (joint form): equal-length suffix dominance gives
    both the `q`-evaluation comparison and the carrying cross-statement, for
    every `q ≥ 1`.  The cons-step adds the `k = 0` suffix condition to the
    `q²`-scaled cross (heads cancel), splitting `q² = 1 + e`. -/
theorem evc_dom_joint (q : Nat) (hq : 1 ≤ q) : ∀ (a b : List Nat),
    a.length = b.length → SuffDom a b →
    evc q a ≤ evc q b ∧ evc q a + evc 1 b ≤ evc q b + evc 1 a
  | [], [], _, _ => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | a :: as, b :: bs, h, hsuf => by
    obtain ⟨ihle, ihcross⟩ := evc_dom_joint q hq as bs (Nat.succ.inj h)
      (fun k => hsuf (k + 1))
    -- q² = 1 + e
    have hq2 : 1 ≤ q ^ 2 := by
      calc 1 = 1 * 1 := rfl
        _ ≤ q * q := Nat.mul_le_mul hq hq
        _ = q ^ 2 := by rw [Nat.pow_succ, Nat.pow_one]
    obtain ⟨e, he⟩ := Nat.le.dest hq2
    -- the scaled cross: q²·evc q as + evc 1 bs ≤ q²·evc q bs + evc 1 as
    have hscaled : q ^ 2 * evc q as + evc 1 bs ≤ q ^ 2 * evc q bs + evc 1 as := by
      calc q ^ 2 * evc q as + evc 1 bs
          = (evc q as + evc 1 bs) + e * evc q as := by rw [← he]; ring_nat
        _ ≤ (evc q bs + evc 1 as) + e * evc q bs :=
            Nat.add_le_add ihcross (Nat.mul_le_mul_left e ihle)
        _ = q ^ 2 * evc q bs + evc 1 as := by rw [← he]; ring_nat
    -- the k = 0 suffix condition
    have h0 : a + evc 1 as ≤ b + evc 1 bs := by
      have := hsuf 0
      show a + evc 1 as ≤ b + evc 1 bs
      calc a + evc 1 as = a + 1 ^ 2 * evc 1 as := by
            rw [show (1 : Nat) ^ 2 = 1 from rfl, Nat.one_mul]
        _ ≤ b + 1 ^ 2 * evc 1 bs := this
        _ = b + evc 1 bs := by
            rw [show (1 : Nat) ^ 2 = 1 from rfl, Nat.one_mul]
    refine ⟨?_, ?_⟩
    · -- add h0 and hscaled, cancel evc1 as + evc1 bs
      have hsum : (a + q ^ 2 * evc q as) + (evc 1 as + evc 1 bs)
          ≤ (b + q ^ 2 * evc q bs) + (evc 1 as + evc 1 bs) := by
        calc (a + q ^ 2 * evc q as) + (evc 1 as + evc 1 bs)
            = (a + evc 1 as) + (q ^ 2 * evc q as + evc 1 bs) := by ring_nat
          _ ≤ (b + evc 1 bs) + (q ^ 2 * evc q bs + evc 1 as) :=
              Nat.add_le_add h0 hscaled
          _ = (b + q ^ 2 * evc q bs) + (evc 1 as + evc 1 bs) := by ring_nat
      exact le_cancel_right hsum
    · -- the cross at cons: heads cancel, reduces to hscaled
      show (a + q ^ 2 * evc q as) + (b + 1 ^ 2 * evc 1 bs)
          ≤ (b + q ^ 2 * evc q bs) + (a + 1 ^ 2 * evc 1 as)
      rw [show (1 : Nat) ^ 2 = 1 from rfl, Nat.one_mul, Nat.one_mul]
      calc (a + q ^ 2 * evc q as) + (b + evc 1 bs)
          = (a + b) + (q ^ 2 * evc q as + evc 1 bs) := by ring_nat
        _ ≤ (a + b) + (q ^ 2 * evc q bs + evc 1 as) := Nat.add_le_add_left hscaled _
        _ = (b + q ^ 2 * evc q bs) + (a + evc 1 as) := by ring_nat

/-- ★★★★★ **Suffix dominance ⟹ evaluation dominance** for every `q ≥ 1`:
    the per-grade content of `LowerBase` reduces to suffix coefficient-sums
    (where the master identity + halving live). -/
theorem evc_dom (q : Nat) (hq : 1 ≤ q) (a b : List Nat)
    (hlen : a.length = b.length) (hsuf : SuffDom a b) :
    evc q a ≤ evc q b :=
  (evc_dom_joint q hq a b hlen hsuf).1

/-- The `LowerBase` reduction through the graded layer: suffix dominance of the
    two explicit convolution lists gives the base inequality at every `q ≥ 1`.
    (The suffix conditions themselves are the remaining master-bridge brick.) -/
theorem lowerbase_of_suffdom (q : Nat) (hq : 1 ≤ q) (i : Nat)
    (hlen : (lmulC (rev (AP (2 * i + 1))) (sListC (2 * i + 1))).length
      = (lmulC (rev (BP (2 * i + 1))) (lsmul (2 * (2 * i + 1) + 1) (cListC (2 * i + 1)))).length)
    (hsuf : SuffDom (lmulC (rev (AP (2 * i + 1))) (sListC (2 * i + 1)))
      (lmulC (rev (BP (2 * i + 1))) (lsmul (2 * (2 * i + 1) + 1) (cListC (2 * i + 1))))) :
    dev q (AP (2 * i + 1)) * sinhNum q (2 * i + 1)
      ≤ (2 * (2 * i + 1) + 1) * dev q (BP (2 * i + 1)) * coshNum q (2 * i + 1) := by
  rw [conn_A q (2 * i + 1) (2 * i + 1), conn_B q (2 * i + 1) (2 * i + 1)]
  exact evc_dom q hq _ _ hlen hsuf

theorem drop_nil : ∀ n, List.drop n ([] : List Nat) = []
  | 0 => rfl
  | _ + 1 => rfl

theorem drop_long : ∀ (n : Nat) (l : List Nat), l.length ≤ n → List.drop n l = []
  | n, [], _ => drop_nil n
  | 0, _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | n + 1, _ :: as, h => drop_long n as (Nat.le_of_succ_le_succ h)

/-- The `i = 1` instance of the remaining suffix brick, machine-checked over
    **all** suffixes (`k ≤ 4` by `decide`; beyond the length both drops vanish). -/
theorem suffdom_one :
    SuffDom (lmulC (rev (AP 3)) (sListC 3)) (lmulC (rev (BP 3)) (lsmul 7 (cListC 3))) := by
  intro k
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | n + 5 =>
    rw [drop_long (n + 5) _ (Nat.le_trans (by decide) (Nat.le_add_left 5 n)),
        drop_long (n + 5) _ (Nat.le_trans (by decide) (Nat.le_add_left 5 n))]
    exact Nat.le_refl 0

/-- ★★★★ **The pipeline closes end-to-end at `i = 1`**: the `LowerBase` base
    inequality for every `q ≥ 1`, derived through the graded layer (suffix
    dominance → Abel transfer → connection) — the general-`i` template. -/
theorem lowerbase_one (q : Nat) (hq : 1 ≤ q) :
    dev q (AP 3) * sinhNum q 3 ≤ 7 * dev q (BP 3) * coshNum q 3 := by
  have h := lowerbase_of_suffdom q hq 1 (by decide) suffdom_one
  exact h

/-! ## §7 — the suffix–convolution recursion (toward general-`i` suffix dominance)

Suffix sums of a convolution obey a clean head-peel recursion: `drop` commutes
with `ladd` and `lsmul`, so

  `Suf k (lmulC (a₀ :: as) b) = a₀·(Suf k b) + Suf (k−1) (lmulC as b)`

(`Suf k l := evc 1 (l.drop k)`; `Nat`-subtraction gives exactly the right
boundary semantics — for `k = 0` the shift contributes its full sum).  This is
the induction vehicle for the remaining brick: the general-`i` suffix
dominance of the two `LowerBase` convolutions. -/

theorem ladd_nil : ∀ l : List Nat, ladd l [] = l
  | [] => rfl
  | _ :: _ => rfl

theorem drop_ladd : ∀ (k : Nat) (a b : List Nat),
    List.drop k (ladd a b) = ladd (List.drop k a) (List.drop k b)
  | 0, _, _ => rfl
  | k + 1, [], b => by
    show List.drop (k + 1) b = ladd [] (List.drop (k + 1) b)
    rfl
  | k + 1, _ :: as, [] => by
    show List.drop k as = ladd (List.drop k as) []
    rw [ladd_nil]
  | k + 1, _ :: as, _ :: bs => by
    show List.drop k (ladd as bs) = ladd (List.drop k as) (List.drop k bs)
    exact drop_ladd k as bs

theorem drop_lsmul : ∀ (k c : Nat) (l : List Nat),
    List.drop k (lsmul c l) = lsmul c (List.drop k l)
  | 0, _, _ => rfl
  | k + 1, c, [] => rfl
  | k + 1, c, _ :: ls => by
    show List.drop k (lsmul c ls) = lsmul c (List.drop k ls)
    exact drop_lsmul k c ls

theorem evc_one_shift (l : List Nat) : evc 1 (0 :: l) = evc 1 l := by
  show 0 + 1 ^ 2 * evc 1 l = evc 1 l
  rw [Nat.zero_add, show (1 : Nat) ^ 2 = 1 from rfl, Nat.one_mul]

/-- ★★★ **The suffix–convolution head-peel**: `Nat`-subtraction handles the
    boundary (`k = 0` keeps the shifted tail whole). -/
theorem suf_cons (k a₀ : Nat) (as b : List Nat) :
    evc 1 (List.drop k (lmulC (a₀ :: as) b))
      = a₀ * evc 1 (List.drop k b) + evc 1 (List.drop (k - 1) (lmulC as b)) := by
  show evc 1 (List.drop k (ladd (lsmul a₀ b) (0 :: lmulC as b))) = _
  rw [drop_ladd, evc_ladd, drop_lsmul, evc_lsmul]
  cases k with
  | zero =>
    show a₀ * evc 1 b + evc 1 (0 :: lmulC as b)
        = a₀ * evc 1 b + evc 1 (lmulC as b)
    rw [evc_one_shift]
  | succ k' => rfl

/-- Length congruence for `lmulC` (what `evc_dom`'s length hypothesis needs,
    without computing the length): componentwise via `ladd`-length congruence. -/
theorem ladd_length_congr : ∀ (a b a' b' : List Nat),
    a.length = a'.length → b.length = b'.length →
    (ladd a b).length = (ladd a' b').length
  | [], b, [], b', _, hb => hb
  | [], _, _ :: _, _, h, _ => Nat.noConfusion h
  | _ :: _, _, [], _, h, _ => Nat.noConfusion h
  | _ :: as, [], _ :: as', [], ha, _ => by
    show as.length + 1 = as'.length + 1
    exact ha
  | _ :: _, [], _ :: _, _ :: _, _, hb => Nat.noConfusion hb
  | _ :: _, _ :: _, _ :: _, [], _, hb => Nat.noConfusion hb
  | _ :: as, b₀ :: bs, _ :: as', b₀' :: bs', ha, hb => by
    show (ladd as bs).length + 1 = (ladd as' bs').length + 1
    exact congrArg (· + 1)
      (ladd_length_congr as bs as' bs' (Nat.succ.inj ha) (Nat.succ.inj hb))

theorem lsmul_length_eq (c : Nat) (l : List Nat) : (lsmul c l).length = l.length :=
  E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld.lsmul_length c l

theorem lmulC_length_congr : ∀ (a b a' b' : List Nat),
    a.length = a'.length → b.length = b'.length →
    (lmulC a b).length = (lmulC a' b').length
  | [], _, [], _, _, _ => rfl
  | [], _, _ :: _, _, h, _ => Nat.noConfusion h
  | _ :: _, _, [], _, h, _ => Nat.noConfusion h
  | a₀ :: as, b, a₀' :: as', b', ha, hb => by
    show (ladd (lsmul a₀ b) (0 :: lmulC as b)).length
        = (ladd (lsmul a₀' b') (0 :: lmulC as' b')).length
    refine ladd_length_congr _ _ _ _ ?_ ?_
    · rw [lsmul_length_eq, lsmul_length_eq]; exact hb
    · show (lmulC as b).length + 1 = (lmulC as' b').length + 1
      exact congrArg (· + 1)
        (lmulC_length_congr as b as' b' (Nat.succ.inj ha) hb)

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly
