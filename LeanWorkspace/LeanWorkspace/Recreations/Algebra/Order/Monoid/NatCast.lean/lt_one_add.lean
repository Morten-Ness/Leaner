import Mathlib

variable {α : Type*}

theorem lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
    [NeZero (1 : α)] [AddRightStrictMono α] (a : α) : a < 1 + a := lt_add_of_pos_left _ zero_lt_one

