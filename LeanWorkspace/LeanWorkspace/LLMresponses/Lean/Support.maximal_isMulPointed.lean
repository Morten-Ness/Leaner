FAIL
import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem maximal_isMulPointed (hMp : M.IsMulPointed) (hMs : M.IsMulSpanning) :
    Maximal Submonoid.IsMulPointed M := by
  classical
  refine ⟨hMp, ?_⟩
  intro P hP hMP
  rw [show P = M by
    apply le_antisymm
    · rw [Submonoid.isMulSpanning_iff] at hMs
      intro g hgP
      obtain ⟨m, hmM, n, hnM, rfl⟩ := hMs g
      have hmP : m ∈ P := hMP hmM
      have hninvP : n⁻¹ ∈ P := hP.inv_mem (hMP hnM)
      simpa [mul_assoc] using P.mul_mem hmP hninvP
    · exact hMP]
