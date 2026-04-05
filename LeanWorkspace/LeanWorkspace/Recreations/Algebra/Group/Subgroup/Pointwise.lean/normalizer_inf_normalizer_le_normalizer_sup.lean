import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem normalizer_inf_normalizer_le_normalizer_sup (H K : Subgroup G) :
    normalizer H ⊓ normalizer K ≤ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro s hs g
  refine ⟨Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf hs g, ?_⟩
  simpa [← mul_assoc] using Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf (inv_mem hs) (s * g * s⁻¹)

