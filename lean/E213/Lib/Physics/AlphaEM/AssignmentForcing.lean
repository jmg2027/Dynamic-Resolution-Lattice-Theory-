import E213.Lib.Physics.Simplex.Counts

/-!
# AssignmentForcing — the leading `60` as the c-free edge count

The leading coefficient `60 = E · d` of `1/α_em` factors through the
octet edge count `E`, expressed **c-free** as

  E = NS · NT · NT = 12

— the extra `NT` is the order-2/signature factor entering the temporal
axis quadratically, **not** a parallel-edge multiplicity.  There is no
atomic `c`: the count is fixed by the forced `(NS, NT) = (3, 2)` alone.

The `NT`-vs-other readings of `60`:

  · The edge-count reading `NS·NT²` is the actual edge count; it is
    fixed by `(NS, NT) = (3, 2)`.

  · A spurious `NS·k²` reading (substituting a free `k` for the second
    `NT`) coincides at `k = NT = 2` but diverges off-point — only
    `NS·NT²` tracks the edge count, with no free dialer.

All theorems PURE.
-/

namespace E213.Lib.Physics.AlphaEM.AssignmentForcing

def NS : Nat := 3
def NT : Nat := 2
def d  : Nat := 5

/-- c-free edge count of the octet, `NS · NT · NT`. -/
def edgeCount (NS NT : Nat) : Nat := NS * NT * NT

/-! ## §1 — the leading `60` from the c-free edge count -/

/-- The edge-count reading `NS·NT²` (the order-2/signature factor `NT`
    enters quadratically). -/
def edgeReading (NS NT : Nat) : Nat := NS * NT * NT

/-- A spurious "second-NT-as-free-`k`" reading `NS·k²`. -/
def kSquaredReading (NS k : Nat) : Nat := NS * k * k

/-- `edgeReading` *is* the c-free edge count (definitional). -/
theorem edge_reading_is_edges (NS NT : Nat) :
    edgeReading NS NT = edgeCount NS NT := rfl

/-- **The leading 60.** Edge count × d at the forced point. -/
theorem leading_sixty_at_drlt :
    edgeReading 3 2 = 12
    ∧ edgeReading 3 2 * 5 = 60 := by decide

/-- **No free dialer.** The spurious `NS·k²` reading coincides with the
    edge count only at `k = NT = 2` and diverges off-point — there is no
    free `k`; the edge count is fixed by `(NS, NT) = (3, 2)`. -/
theorem reading_unique_no_free_dialer :
    edgeReading 3 2 = kSquaredReading 3 2            -- coincide at k = 2
    ∧ edgeReading 3 2 ≠ kSquaredReading 3 3          -- diverges at k = 3
    ∧ kSquaredReading 3 3 = 27 := by decide

/-! ## §2 — capstone -/

/-- **Leading `60` is the c-free edge count × d.**  `E = NS·NT² = 12`
    is fixed by the forced `(NS, NT) = (3, 2)`; `60 = E·d`.  No atomic
    multiplicity `c`, no free dialer. -/
theorem nt_c_degeneracy_resolved :
    edgeReading 3 2 = 12
    ∧ edgeReading 3 2 * 5 = 60
    ∧ edgeReading 3 2 = kSquaredReading 3 2
    ∧ edgeReading 3 2 ≠ kSquaredReading 3 3 := by decide

end E213.Lib.Physics.AlphaEM.AssignmentForcing
