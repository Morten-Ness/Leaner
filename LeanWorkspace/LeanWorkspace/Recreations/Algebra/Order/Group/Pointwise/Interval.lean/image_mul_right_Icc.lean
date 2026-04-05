import Mathlib

variable {α : Type*}

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

theorem image_mul_right_Icc (hab : a ≤ b) (hc : 0 ≤ c) :
    (· * c) '' Icc a b = Icc (a * c) (b * c) := by
  cases eq_or_lt_of_le hc
  · subst c
    simp [(nonempty_Icc.2 hab).image_const]
  exact Set.image_mul_right_Icc' a b ‹0 < c›

