import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem div_lt_of_mabs_div_lt_left (h : |a / b|ₘ < c) : b / c < a := div_lt_comm.1 <| (mabs_div_lt_iff.1 h).2

