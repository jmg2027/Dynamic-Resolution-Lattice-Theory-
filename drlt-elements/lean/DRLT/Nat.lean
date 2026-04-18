/-
  DRLT Elements — Phase 1-3: Nat (natural numbers from Entity)
  Joint research by Mingu Jeong and Claude (Anthropic)

  Canonical encoding: point = 0, pair point x = succ(x)
  All definitions use recursors directly (no equation compiler).
-/
prelude
import DRLT.Logic

-- ═══ Entity → Nat encoding ═══
-- encode n: point for 0, pair point (encode k) for succ k
noncomputable def Entity.encode (n : Nat) : Entity :=
  @Nat.rec (fun _ => Entity)
    Entity.point
    (fun _ ih => Entity.pair Entity.point ih)
    n

-- decode e: point→0, pair point b→succ(decode b), else→0
noncomputable def Entity.decode (e : Entity) : Nat :=
  @Entity.rec (fun _ => Nat)
    Nat.zero
    (fun a _ _ db =>
      @Entity.rec (fun _ => Nat)
        (Nat.succ db)
        (fun _ _ _ _ => Nat.zero)
        a)
    e

-- ═══ Round-trip: decode ∘ encode = id ═══
theorem decode_encode (n : Nat) :
    Eq (Entity.decode (Entity.encode n)) n :=
  @Nat.rec (fun n => Eq (Entity.decode (Entity.encode n)) n)
    (Eq.refl Nat.zero)
    (fun _ ih => Eq.congr Nat.succ ih)
    n

-- ═══ Weak direction: encode ∘ decode ∘ encode = encode ═══
theorem encode_decode_encode (n : Nat) :
    Eq (Entity.encode (Entity.decode (Entity.encode n)))
       (Entity.encode n) :=
  Eq.congr Entity.encode (decode_encode n)
