import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem Nat.cast_le_pow_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ a ^ n / (a - 1) := (n.cast_le_pow_sub_div_sub H).trans <|
    div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.2 H.le)

