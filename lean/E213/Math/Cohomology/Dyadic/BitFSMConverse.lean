import E213.Math.Cohomology.Dyadic.BitFSMBound

/-!
# BitFSM converse — periodic bit stream ⇒ ∃ BitFSM

Constructs an explicit BitFSM(p) for any purely periodic bit
stream with period p.  Combined with `fsm_bits_eventually_periodic`,
gives a logical equivalence at Tier 0:

  bs purely periodic with period p ⇔ ∃ BitFSM(p) generating bs.

Construction: cyclic shift register.  State v ∈ Fin p; step
v → ⟨(v+1) % p, _⟩; out v := bs v.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- BitFSM cyclic shift register for period-p stream. -/
def bitFSMOfPure (bs : Nat → Bool) (p : Nat) (hp : 0 < p) : BitFSM p where
  init := ⟨0, hp⟩
  step v := ⟨(v.val + 1) % p, Nat.mod_lt _ hp⟩
  out v := bs v.val

/-- The cyclic FSM run at step k is ⟨k % p, _⟩. -/
theorem bitFSMOfPure_run (bs : Nat → Bool) (p : Nat) (hp : 0 < p) :
    ∀ k, (bitFSMOfPure bs p hp).run k = ⟨k % p, Nat.mod_lt _ hp⟩ := by
  intro k
  induction k with
  | zero => apply Fin.ext; show 0 = 0 % p; rw [Nat.zero_mod]
  | succ k' ih =>
    show (bitFSMOfPure bs p hp).step ((bitFSMOfPure bs p hp).run k')
        = ⟨(k' + 1) % p, _⟩
    rw [ih]
    apply Fin.ext
    show (k' % p + 1) % p = (k' + 1) % p
    exact Nat.mod_add_mod k' p 1

/-- ★★★ Cyclic FSM bits = bs (mod p): bits k = bs (k % p). -/
theorem bitFSMOfPure_bits (bs : Nat → Bool) (p : Nat) (hp : 0 < p) :
    ∀ k, (bitFSMOfPure bs p hp).bits k = bs (k % p) := by
  intro k
  show (bitFSMOfPure bs p hp).out ((bitFSMOfPure bs p hp).run k) = bs (k % p)
  rw [bitFSMOfPure_run]
  rfl

/-- ★★★★★ For purely periodic bs, the cyclic FSM matches bs exactly. -/
theorem bitFSMOfPure_correct (bs : Nat → Bool) (p : Nat) (hp : 0 < p)
    (hbs : ∀ n, bs (n + p) = bs n) :
    ∀ k, (bitFSMOfPure bs p hp).bits k = bs k := by
  intro k
  rw [bitFSMOfPure_bits]
  have h1 : k % p + (k / p) * p = k := by
    rw [Nat.mul_comm]; exact Nat.mod_add_div k p
  have h2 : bs ((k % p) + (k / p) * p) = bs (k % p) :=
    bs_periodic_multiple bs p hbs (k / p) (k % p)
  rw [h1] at h2
  exact h2.symm

/-- ★★★★★★ Tier 0 EQUIVALENCE: bs purely periodic ⇔ ∃ BitFSM matching bs. -/
theorem tier0_equiv_bitfsm (bs : Nat → Bool) (p : Nat) (hp : 0 < p)
    (hbs : ∀ n, bs (n + p) = bs n) :
    ∃ (m : BitFSM p), ∀ k, m.bits k = bs k :=
  ⟨bitFSMOfPure bs p hp, bitFSMOfPure_correct bs p hp hbs⟩

end E213.Math.Cohomology.Dyadic.Conjecture
