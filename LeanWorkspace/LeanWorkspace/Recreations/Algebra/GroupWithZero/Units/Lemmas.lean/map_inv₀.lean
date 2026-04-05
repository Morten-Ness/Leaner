import Mathlib

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
  [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (a b : G₀)

theorem map_inv₀ : f a⁻¹ = (f a)⁻¹ := by
  by_cases h : a = 0
  · simp [h, map_zero f]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel₀ h, map_one]

