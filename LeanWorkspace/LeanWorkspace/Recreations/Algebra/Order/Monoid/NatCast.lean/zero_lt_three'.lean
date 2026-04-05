import Mathlib

variable {α : Type*}

variable [AddMonoidWithOne α]

variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

variable [AddLeftMono α]

theorem zero_lt_three' : (0 : α) < 3 := zero_lt_three

