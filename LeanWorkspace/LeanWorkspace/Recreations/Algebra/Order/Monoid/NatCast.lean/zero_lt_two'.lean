import Mathlib

variable {α : Type*}

variable [AddMonoidWithOne α]

variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

variable [AddLeftMono α]

theorem zero_lt_two' : (0 : α) < 2 := zero_lt_two

