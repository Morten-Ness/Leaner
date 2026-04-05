import Mathlib

variable {α : Type u}

theorem invOf_one [Monoid α] [Invertible (1 : α)] : ⅟(1 : α) = 1 := invOf_one'

