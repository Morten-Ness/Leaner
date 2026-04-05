import Mathlib

variable {F α β γ : Type*}

variable [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β] (m : F) {s t : Set α}

theorem mul_subset_range {s t : Set β} (hs : s ⊆ range m) (ht : t ⊆ range m) : s * t ⊆ range m := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, rfl⟩ := hs ha
  obtain ⟨b, rfl⟩ := ht hb
  exact ⟨a * b, map_mul ..⟩

