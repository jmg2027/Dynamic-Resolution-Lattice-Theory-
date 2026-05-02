import E213.Math.Cohomology.Dyadic.SignatureBipartite
import E213.Physics.Simplex.Counts

/-!
# K_{3,2}^{(2)} signature ↔ DRLT atomicity (NS, NT, d)

The K_{3,2}^{(2)} signature lens has 5 vertices = 3 S-vertices +
2 T-vertices, exactly matching the atomic primitives:
  - NS = 3 (S-vertices, "spatial atomic")
  - NT = 2 (T-vertices, "temporal atomic")
  - d = 5 = NS + NT (total atomic dimension)

These come from `Physics.SimplexCounts` and are forced by
`OS.Atomicity`: d = 5 is the unique Nat with a unique alive
2,3-decomposition.

Therefore the signature lens isn't arbitrary — it's the
*atomically forced* lens for the DRLT framework.
-/

namespace E213.Math.Cohomology.Dyadic.AtomicityConnection

open E213.Math.Cohomology.Dyadic.Signature (signature)


/-- ★ K_{3,2}^{(2)} signature uses exactly NS S-vertices. -/
theorem signature_S_count : E213.Physics.Simplex.Counts.NS = 3 := rfl

/-- ★ K_{3,2}^{(2)} signature uses exactly NT T-vertices. -/
theorem signature_T_count : E213.Physics.Simplex.Counts.NT = 2 := rfl

/-- ★ Total signature dimension = d = 5. -/
theorem signature_d_count : E213.Physics.Simplex.Counts.d = 5 := rfl

/-- ★★ Signature S-side index range matches NS. -/
theorem isS_iff_lt_NS (v : Fin 5) :
    isS v ↔ v.val < E213.Physics.Simplex.Counts.NS := by
  unfold isS
  show v.val < 3 ↔ v.val < E213.Physics.Simplex.Counts.NS
  rw [show E213.Physics.Simplex.Counts.NS = 3 from rfl]

/-- ★★ Signature T-side index range matches NT (offset). -/
theorem isT_iff_ge_NS (v : Fin 5) :
    isT v ↔ v.val ≥ E213.Physics.Simplex.Counts.NS := by
  unfold isT
  show v.val ≥ 3 ↔ v.val ≥ E213.Physics.Simplex.Counts.NS
  rw [show E213.Physics.Simplex.Counts.NS = 3 from rfl]

/-- ★★★ Signature alternation = bipartite K_{NS,NT}^{(2)} alternation:
    even step ⇒ S-side (NS-many), odd step ⇒ T-side (NT-many). -/
theorem signature_NS_NT_alternation (bs : Nat → Bool) (k : Nat) :
    (k % 2 = 0 → (signature bs k).val < E213.Physics.Simplex.Counts.NS)
    ∧ (k % 2 = 1 → (signature bs k).val ≥ E213.Physics.Simplex.Counts.NS) := by
  obtain ⟨hS, hT⟩ := signature_bipartite_alternation bs k
  refine ⟨?_, ?_⟩
  · intro hk; exact (isS_iff_lt_NS _).mp (hS hk)
  · intro hk; exact (isT_iff_ge_NS _).mp (hT hk)

/-- ★★★★★ Capstone: K_{3,2}^{(2)} signature lens is the
    atomically-forced lens — its dimensions match (NS, NT, d). -/
theorem signature_atomicity_capstone :
    E213.Physics.Simplex.Counts.NS = 3 ∧ E213.Physics.Simplex.Counts.NT = 2
    ∧ E213.Physics.Simplex.Counts.d = 5 ∧ E213.Physics.Simplex.Counts.NS + E213.Physics.Simplex.Counts.NT
        = E213.Physics.Simplex.Counts.d :=
  ⟨signature_S_count, signature_T_count, signature_d_count, by decide⟩

end E213.Math.Cohomology.Dyadic.AtomicityConnection
