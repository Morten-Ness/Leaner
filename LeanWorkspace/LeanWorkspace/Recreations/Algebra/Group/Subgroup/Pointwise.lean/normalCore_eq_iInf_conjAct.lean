import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem normalCore_eq_iInf_conjAct (H : Subgroup G) :
    H.normalCore = ⨅ (g : ConjAct G), g • H := by
  ext g
  simp only [Subgroup.normalCore, Subgroup.mem_iInf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  refine ⟨fun h x ↦ h x⁻¹, fun h x ↦ ?_⟩
  simpa only [ConjAct.toConjAct_inv, inv_inv] using h x⁻¹

