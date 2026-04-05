import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_sub_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x - ofNat(n)) = round x - ofNat(n) := round_sub_natCast x n

