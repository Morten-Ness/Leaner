import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem div_le_of_mabs_div_le_left (h : |a / b|ₘ ≤ c) : b / c ≤ a := div_le_comm.1 <| (mabs_div_le_iff.1 h).2

