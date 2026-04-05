import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem eq_of_mabs_div_eq_one {a b : G} (h : |a / b|ₘ = 1) : a = b := div_eq_one.1 <| mabs_eq_one.1 h

