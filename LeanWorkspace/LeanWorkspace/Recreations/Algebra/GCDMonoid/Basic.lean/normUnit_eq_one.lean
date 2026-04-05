import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [Subsingleton αˣ]

theorem normUnit_eq_one (x : α) : normUnit x = 1 := rfl

