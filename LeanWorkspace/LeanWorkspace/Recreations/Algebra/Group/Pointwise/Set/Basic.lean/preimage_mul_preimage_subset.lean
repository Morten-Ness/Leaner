import Mathlib

variable {F α β γ : Type*}

variable [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β] (m : F) {s t : Set α}

theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_mul m ..).symm⟩

