import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem conj_smul_eq_self_of_mem {H : Subgroup G} {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  refine le_antisymm ?_ ?_
  · exact (Subgroup.conj_smul_le_of_le (le_refl H) ⟨h, hh⟩)
  · rw [Subgroup.subset_pointwise_smul_iff, ← map_inv]
    exact Subgroup.conj_smul_le_of_le (le_refl H) ⟨h⁻¹, H.inv_mem hh⟩

