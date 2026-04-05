import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [Subsingleton αˣ]

theorem normalize_eq (x : α) : normalize x = x := mul_one x

