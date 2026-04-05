import Mathlib

variable {α : Type*}

theorem zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 := zero_le_one

