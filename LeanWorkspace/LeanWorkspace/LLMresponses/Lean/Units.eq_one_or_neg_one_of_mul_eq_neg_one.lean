import Mathlib

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_neg_one (h : u * v = -1) : u = 1 ∨ u = -1 := by
  have hu : IsUnit u := by
    refine ⟨⟨u, -v, ?_, ?_⟩, rfl⟩
    · calc
        u * (-v) = -(u * v) := by ring
        _ = -(-1) := by rw [h]
        _ = 1 := by norm_num
    · calc
        (-v) * u = -(v * u) := by ring
        _ = -(u * v) := by rw [mul_comm]
        _ = -(-1) := by rw [h]
        _ = 1 := by norm_num
  simpa [Int.isUnit_iff] using hu
