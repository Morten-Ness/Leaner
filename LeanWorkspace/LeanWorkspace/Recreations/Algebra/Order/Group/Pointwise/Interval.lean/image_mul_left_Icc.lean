import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

theorem image_mul_left_Icc (ha : 0 ≤ a) (hbc : b ≤ c) :
    (a * ·) '' Icc b c = Icc (a * b) (a * c) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [(nonempty_Icc.2 hbc).image_const]
  · exact Set.image_mul_left_Icc' ha b c

