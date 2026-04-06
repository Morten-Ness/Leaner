FAIL
import Mathlib

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_one' (h : u * v = 1) : u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  have hu : IsUnit u := by
    rw [Int.isUnit_iff]
    have : v = u⁻¹ := by
      apply mul_right_cancel₀ (a := u)
      · exact Int.ne_zero_of_mul_eq_one_right h
      · rw [mul_inv_cancel₀ (Int.ne_zero_of_mul_eq_one_left h), h, one_mul]
    rcases Int.isUnit_iff.mp (by
      exact ⟨rfl⟩) with hu' | hu'
    · exact Or.inl hu'
    · exact Or.inr hu'
  rcases Int.isUnit_iff.mp hu with hu' | hu'
  · left
    constructor
    · exact hu'
    · apply mul_left_cancel₀ (a := u)
      · rw [hu']
        norm_num
      · rw [hu', one_mul] at h
        exact h
  · right
    constructor
    · exact hu'
    · apply mul_left_cancel₀ (a := u)
      · rw [hu']
        norm_num
      · rw [hu', neg_one_mul] at h
        exact h
