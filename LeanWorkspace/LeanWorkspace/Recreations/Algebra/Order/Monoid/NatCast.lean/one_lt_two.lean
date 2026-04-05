import Mathlib

variable {α : Type*}

variable [AddMonoidWithOne α]

variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

theorem one_lt_two [AddLeftStrictMono α] : (1 : α) < 2 := by
  rw [← one_add_one_eq_two]
  exact lt_add_one _

