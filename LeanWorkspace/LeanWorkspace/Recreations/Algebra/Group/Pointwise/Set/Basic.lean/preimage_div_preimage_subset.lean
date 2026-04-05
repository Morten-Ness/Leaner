import Mathlib

variable {F α β γ : Type*}

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (m : F) {s t : Set α}

theorem preimage_div_preimage_subset {s t : Set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_div m ..).symm⟩

