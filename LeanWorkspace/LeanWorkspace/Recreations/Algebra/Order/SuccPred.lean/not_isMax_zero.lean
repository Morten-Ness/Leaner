import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem not_isMax_zero [Zero α] [One α] [ZeroLEOneClass α] [NeZero (1 : α)] : ¬ IsMax (0 : α) := by
  rw [not_isMax_iff]
  exact ⟨1, one_pos⟩

