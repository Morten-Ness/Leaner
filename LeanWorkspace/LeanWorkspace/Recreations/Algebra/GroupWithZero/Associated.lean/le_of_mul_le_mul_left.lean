import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem le_of_mul_le_mul_left (a b c : Associates M) (ha : a ≠ 0) : a * b ≤ a * c → b ≤ c
  | ⟨d, hd⟩ => ⟨d, mul_left_cancel₀ ha <| by rwa [← mul_assoc]⟩
