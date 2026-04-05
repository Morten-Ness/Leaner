import Mathlib

variable {α : Type*}

variable [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

theorem zero_lt_one' : (0 : α) < 1 := zero_lt_one

