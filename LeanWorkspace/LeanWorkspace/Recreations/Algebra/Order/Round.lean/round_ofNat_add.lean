import Mathlib

variable {F α β : Type*}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_ofNat_add (n : ℕ) [n.AtLeastTwo] (x : α) :
    round (ofNat(n) + x) = ofNat(n) + round x := round_natCast_add x n

