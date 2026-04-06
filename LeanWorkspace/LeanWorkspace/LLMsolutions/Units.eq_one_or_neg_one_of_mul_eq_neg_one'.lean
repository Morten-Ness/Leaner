FAIL
import Mathlib

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_neg_one' (h : u * v = -1) : u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  have h' : IsUnit (u * v) := by
    rw [h]
    norm_num
  have hu : IsUnit u := IsUnit.of_mul_isUnit_left h'
  rcases Int.isUnit_iff.mp hu with rfl | rfl
  · left
    constructor
    · rfl
    · simpa using h
  · right
    constructor
    · rfl
    · linarith [h]
