import E213.Lib.Physics.Simplex.Counts

/-!
# m_t/m_c — quark-mass chain atomic skeleton sum (0 axioms)

DRLT atomic reading (per `catalogs/physics-constants.md`):

  m_t / m_c chain composition assembles from the QuarkHierarchy
  atomic factors.  The integer skeleton before any ζ(2) / α_GUT
  correction is

    mt_mc_chain_sum = NS·d² + NS·NT² = 75 + 12 = 87.

PDG values (MS-bar masses): m_t = 172.76 GeV, m_c = 1.27 GeV,
→ m_t/m_c ≈ 136.0.  The chain skeleton 87 is the *bare* integer
sum; it is **not** 1/α_em(IR) = 137, and no underived constant is
added here to force the two together.

All theorems below are **PURE** via `decide`.
-/

namespace E213.Lib.Physics.Hadron.MtOverMc

open E213.Lib.Physics.Simplex.Counts

/-- The m_t/m_c chain composition atomic sum (per QuarkHierarchy):
    leading NS·d² = 75, constant NS·NT² = 12.  Sum 87 is the bare
    integer skeleton from the atomic factors. -/
def mt_mc_chain_sum : Nat := NS * (d * d) + NS * (NT * NT)

theorem mt_mc_chain_sum_value : mt_mc_chain_sum = 87 := by decide

/-- m_t/m_c chain skeleton: the bare integer sum 87 = NS·(d² + NT²)
    from the QuarkHierarchy atomic factors.  PURE. -/
theorem mt_mc_chain_skeleton :
    mt_mc_chain_sum = 87
    ∧ mt_mc_chain_sum = NS * (d * d + NT * NT)
    ∧ NS = 3 ∧ NT = 2 ∧ d = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Hadron.MtOverMc
