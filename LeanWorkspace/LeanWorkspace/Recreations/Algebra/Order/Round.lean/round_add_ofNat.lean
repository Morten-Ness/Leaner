import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_add_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x + ofNat(n)) = round x + ofNat(n) := round_add_natCast x n

