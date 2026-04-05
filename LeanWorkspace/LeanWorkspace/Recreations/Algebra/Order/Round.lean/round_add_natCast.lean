import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_add_natCast (x : α) (y : ℕ) : round (x + y) = round x + y := mod_cast round_add_intCast x y

