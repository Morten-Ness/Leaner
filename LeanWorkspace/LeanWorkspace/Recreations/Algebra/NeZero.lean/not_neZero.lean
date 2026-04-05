import Mathlib

variable {R : Type*} [Zero R]

theorem not_neZero {n : R} : ¬NeZero n ↔ n = 0 := by simp [neZero_iff]

