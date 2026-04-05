import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_ofNat (n : ℕ) [n.AtLeastTwo] : round (ofNat(n) : α) = ofNat(n) := round_natCast n

