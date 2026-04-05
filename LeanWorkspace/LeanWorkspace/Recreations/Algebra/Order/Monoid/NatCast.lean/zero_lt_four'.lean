import Mathlib

variable {α : Type*}

variable [AddMonoidWithOne α]

variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

variable [AddLeftMono α]

theorem zero_lt_four' : (0 : α) < 4 := zero_lt_four

