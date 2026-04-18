/-
  DRLT Elements — Phase 1-5: Order (≤, <, decidability)
  Joint research by Mingu Jeong and Claude (Anthropic)

  All proofs term-mode, recursors only. No tactics.
-/
prelude
import DRLT.Arithmetic

-- ═══ Order ═══
def DRLT.le (a b : Nat) : Prop :=
  Exists (fun k => Eq (DRLT.add a k) b)

def DRLT.lt (a b : Nat) : Prop :=
  DRLT.le (Nat.succ a) b

-- ═══ le: reflexivity ═══
theorem DRLT.le_refl (a : Nat) : DRLT.le a a :=
  @Exists.intro Nat (fun k => Eq (DRLT.add a k) a)
    Nat.zero (DRLT.add_zero a)

-- ═══ le: 0 ≤ n ═══
theorem DRLT.zero_le (n : Nat) : DRLT.le Nat.zero n :=
  @Exists.intro Nat (fun k => Eq (DRLT.add Nat.zero k) n)
    n (Eq.refl n)

-- ═══ Helpers ═══
noncomputable def Nat.pred (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) Nat.zero (fun k _ => k) n

theorem DRLT.succ_inj {a b : Nat}
    (h : Eq (Nat.succ a) (Nat.succ b)) : Eq a b :=
  Eq.congr Nat.pred h

theorem DRLT.succ_ne_zero (n : Nat)
    (h : Eq (Nat.succ n) Nat.zero) : False :=
  @Eq.rec Nat (Nat.succ n)
    (fun m _ => @Nat.rec (fun _ => Prop) False (fun _ _ => True) m)
    True.intro Nat.zero h

-- ═══ le: succ preserves ═══
theorem DRLT.succ_le_succ {a b : Nat}
    (h : DRLT.le a b) : DRLT.le (Nat.succ a) (Nat.succ b) :=
  @Exists.rec Nat (fun k => Eq (DRLT.add a k) b)
    (fun _ => DRLT.le (Nat.succ a) (Nat.succ b))
    (fun k hk =>
      @Exists.intro Nat
        (fun k => Eq (DRLT.add (Nat.succ a) k) (Nat.succ b))
        k (Eq.congr Nat.succ hk))
    h

-- ═══ le: predecessor ═══
theorem DRLT.le_of_succ {a b : Nat}
    (h : DRLT.le (Nat.succ a) (Nat.succ b)) : DRLT.le a b :=
  @Exists.rec Nat
    (fun k => Eq (DRLT.add (Nat.succ a) k) (Nat.succ b))
    (fun _ => DRLT.le a b)
    (fun k hk =>
      @Exists.intro Nat (fun k => Eq (DRLT.add a k) b)
        k (DRLT.succ_inj hk))
    h

-- ═══ not succ ≤ zero ═══
theorem DRLT.not_succ_le_zero (a : Nat) :
    DRLT.le (Nat.succ a) Nat.zero → False :=
  fun h =>
    @Exists.rec Nat
      (fun k => Eq (DRLT.add (Nat.succ a) k) Nat.zero)
      (fun _ => False)
      (fun _ hk => DRLT.succ_ne_zero _ hk)
      h

-- ═══ Decidable le ═══
noncomputable def DRLT.decLe (a b : Nat) :
    Decidable (DRLT.le a b) :=
  @Nat.rec (fun a => (b : Nat) → Decidable (DRLT.le a b))
    (fun b => Decidable.isTrue (DRLT.zero_le b))
    (fun a' ih b =>
      @Nat.rec (fun b => Decidable (DRLT.le (Nat.succ a') b))
        (Decidable.isFalse (DRLT.not_succ_le_zero a'))
        (fun b' _ =>
          @Decidable.rec (DRLT.le a' b')
            (fun _ => Decidable (DRLT.le (Nat.succ a') (Nat.succ b')))
            (fun hn => Decidable.isFalse
              (fun h2 => hn (DRLT.le_of_succ h2)))
            (fun hp => Decidable.isTrue (DRLT.succ_le_succ hp))
            (ih b'))
        b)
    a b
