import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem mem_smul_set_inv {s : Set α} : a ∈ b • s⁻¹ ↔ b ∈ a • s := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y⁻¹, ?_, ?_⟩
    · simpa using hy
    · simp [mul_assoc]
  · rintro ⟨y, hy, h⟩
    refine ⟨y⁻¹, ?_, ?_⟩
    · simpa using hy
    · rw [← h]
      simp [mul_assoc]
