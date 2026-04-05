import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LinearOrder α] [MulLeftMono α] [MulRightMono α] {a b c d : α}

theorem min_mul_min_le_min_mul_mul' : min a c * min b d ≤ min (a * b) (c * d) := le_min (mul_le_mul' (min_le_left _ _) <| min_le_left _ _) <|
    mul_le_mul' (min_le_right _ _) <| min_le_right _ _

