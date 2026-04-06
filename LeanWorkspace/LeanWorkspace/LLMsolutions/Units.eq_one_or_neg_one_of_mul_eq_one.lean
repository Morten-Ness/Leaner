import Mathlib

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_one (h : u * v = 1) : u = 1 ∨ u = -1 := by
  have hu : IsUnit u := by
    refine ⟨⟨u, v, h, ?_⟩, rfl⟩
    simpa [mul_comm] using h
  simpa [Int.isUnit_iff] using hu
