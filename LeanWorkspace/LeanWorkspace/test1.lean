import Mathlib

theorem isComplement_singleton_left {G : Type*} [Group G] {S : Set G} {g : G} :
  Subgroup.IsComplement ({g} : Set G) S ↔ S = Set.univ := by
  refine ⟨fun ⟨_, h_surj⟩ => top_le_iff.mp ?_, fun h => h.symm ▸ Subgroup.isComplement_singleton_univ⟩
  intro x _
  obtain ⟨⟨⟨_, rfl⟩, ⟨s, hs⟩⟩, hmul⟩ := h_surj (g * x)
  exact mul_left_cancel hmul ▸ hs
