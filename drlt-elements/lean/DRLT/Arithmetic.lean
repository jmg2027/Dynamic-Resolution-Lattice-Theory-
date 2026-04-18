/-
  DRLT Elements — Phase 1-4: Arithmetic (addition, multiplication)
  Joint research by Mingu Jeong and Claude (Anthropic)

  All proofs are term-mode (Nat.rec + Eq.*). No tactics.
  Definitions use Nat.rec directly (prelude: no equation compiler).
-/
prelude
import DRLT.Nat

-- ═══ Addition ═══
noncomputable def DRLT.add (a b : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) b (fun _ ih => Nat.succ ih) a

-- ═══ Multiplication ═══
noncomputable def DRLT.mul (a b : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) Nat.zero (fun _ ih => DRLT.add b ih) a

-- ═══ add: right identity  (a + 0 = a) ═══
theorem DRLT.add_zero (a : Nat) : Eq (DRLT.add a Nat.zero) a :=
  @Nat.rec (fun a => Eq (DRLT.add a Nat.zero) a)
    (Eq.refl Nat.zero)
    (fun _ ih => Eq.congr Nat.succ ih)
    a

-- ═══ add: right successor  (a + succ b = succ (a + b)) ═══
theorem DRLT.add_succ (a b : Nat) :
    Eq (DRLT.add a (Nat.succ b)) (Nat.succ (DRLT.add a b)) :=
  @Nat.rec (fun a => Eq (DRLT.add a (Nat.succ b)) (Nat.succ (DRLT.add a b)))
    (Eq.refl (Nat.succ b))
    (fun _ ih => Eq.congr Nat.succ ih)
    a

-- ═══ add: commutativity  (a + b = b + a) ═══
theorem DRLT.add_comm (a b : Nat) : Eq (DRLT.add a b) (DRLT.add b a) :=
  @Nat.rec (fun a => Eq (DRLT.add a b) (DRLT.add b a))
    (Eq.symm (DRLT.add_zero b))
    (fun n ih =>
      Eq.trans (Eq.congr Nat.succ ih) (Eq.symm (DRLT.add_succ b n)))
    a

-- ═══ add: associativity  ((a+b)+c = a+(b+c)) ═══
theorem DRLT.add_assoc (a b c : Nat) :
    Eq (DRLT.add (DRLT.add a b) c) (DRLT.add a (DRLT.add b c)) :=
  @Nat.rec (fun a => Eq (DRLT.add (DRLT.add a b) c) (DRLT.add a (DRLT.add b c)))
    (Eq.refl (DRLT.add b c))
    (fun _ ih => Eq.congr Nat.succ ih)
    a

-- ═══ Helper: 4-element swap  ((a+b)+(c+d) = (a+c)+(b+d)) ═══
theorem DRLT.add_four_swap (a b c d : Nat) :
    Eq (DRLT.add (DRLT.add a b) (DRLT.add c d))
       (DRLT.add (DRLT.add a c) (DRLT.add b d)) :=
  let s1 := DRLT.add_assoc a b (DRLT.add c d)
  let s2 := Eq.symm (DRLT.add_assoc b c d)
  let s3 := DRLT.add_comm b c
  let s4 := Eq.congr (fun x => DRLT.add x d) s3
  let s5 := DRLT.add_assoc c b d
  let s6 := Eq.trans s2 (Eq.trans s4 s5)
  let s7 := Eq.congr (DRLT.add a) s6
  let s8 := Eq.symm (DRLT.add_assoc a c (DRLT.add b d))
  Eq.trans s1 (Eq.trans s7 s8)

-- ═══ mul: right zero  (a * 0 = 0) ═══
theorem DRLT.mul_zero (a : Nat) : Eq (DRLT.mul a Nat.zero) Nat.zero :=
  @Nat.rec (fun a => Eq (DRLT.mul a Nat.zero) Nat.zero)
    (Eq.refl Nat.zero)
    (fun _ ih => ih)
    a

-- ═══ mul: right successor  (a * succ b = a*b + a) ═══
theorem DRLT.mul_succ (a b : Nat) :
    Eq (DRLT.mul a (Nat.succ b)) (DRLT.add (DRLT.mul a b) a) :=
  @Nat.rec (fun a => Eq (DRLT.mul a (Nat.succ b)) (DRLT.add (DRLT.mul a b) a))
    (Eq.refl Nat.zero)
    (fun n ih =>
      let s1 := Eq.congr (DRLT.add (Nat.succ b)) ih
      let s2 := DRLT.add_succ (DRLT.add b (DRLT.mul n b)) n
      let s3 := DRLT.add_assoc b (DRLT.mul n b) n
      let s4 := Eq.congr Nat.succ s3
      Eq.trans s1 (Eq.symm (Eq.trans s2 s4)))
    a

-- ═══ mul: commutativity  (a * b = b * a) ═══
theorem DRLT.mul_comm (a b : Nat) : Eq (DRLT.mul a b) (DRLT.mul b a) :=
  @Nat.rec (fun a => Eq (DRLT.mul a b) (DRLT.mul b a))
    (Eq.symm (DRLT.mul_zero b))
    (fun n ih =>
      let s1 := Eq.congr (DRLT.add b) ih
      let s2 := DRLT.add_comm b (DRLT.mul b n)
      let s3 := Eq.symm (DRLT.mul_succ b n)
      Eq.trans s1 (Eq.trans s2 s3))
    a

-- ═══ mul: left distributivity  (a*(b+c) = a*b + a*c) ═══
theorem DRLT.left_distrib (a b c : Nat) :
    Eq (DRLT.mul a (DRLT.add b c))
       (DRLT.add (DRLT.mul a b) (DRLT.mul a c)) :=
  @Nat.rec (fun a => Eq (DRLT.mul a (DRLT.add b c))
                        (DRLT.add (DRLT.mul a b) (DRLT.mul a c)))
    (Eq.refl Nat.zero)
    (fun n ih =>
      let s1 := Eq.congr (DRLT.add (DRLT.add b c)) ih
      Eq.trans s1 (DRLT.add_four_swap b c (DRLT.mul n b) (DRLT.mul n c)))
    a
