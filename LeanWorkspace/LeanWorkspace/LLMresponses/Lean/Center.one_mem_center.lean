import Mathlib

variable {M : Type*} {S T : Set M}

variable [MulOneClass M]

theorem one_mem_center : (1 : M) ∈ Set.center M where
  comm _ := by simp
  left_assoc _ _ := by simp
  right_assoc _ _ := by simp
