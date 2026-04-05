import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LinearOrder α] [MulLeftMono α] [MulRightMono α] {a b c d : α}

theorem max_mul_mul_le_max_mul_max' : max (a * b) (c * d) ≤ max a c * max b d := max_le (mul_le_mul' (le_max_left _ _) <| le_max_left _ _) <|
    mul_le_mul' (le_max_right _ _) <| le_max_right _ _

