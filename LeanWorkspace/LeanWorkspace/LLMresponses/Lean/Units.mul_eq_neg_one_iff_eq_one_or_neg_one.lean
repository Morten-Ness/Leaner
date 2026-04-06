FAIL
import Mathlib

variable {u v : ℤ}

theorem mul_eq_neg_one_iff_eq_one_or_neg_one : u * v = -1 ↔ u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  constructor
  · intro h
    have hu : IsUnit u := by
      refine isUnit_of_mul_eq_one ?_
      use -v
      linarith [h]
    have hv : IsUnit v := by
      refine isUnit_of_mul_eq_one ?_
      use -u
      linarith [h]
    have hu' : u = 1 ∨ u = -1 := by
      rcases Int.isUnit_iff.mp hu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hv' : v = 1 ∨ v = -1 := by
      rcases Int.isUnit_iff.mp hv with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> norm_num at h ⊢
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
