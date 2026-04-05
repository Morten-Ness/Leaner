import Mathlib

variable {α : Type*}

theorem lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
    [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1 := lt_add_of_pos_right _ zero_lt_one

