import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem eq_of_mabs_div_lt_all {x y : G} (h : ∀ ε > 1, |x / y|ₘ < ε) : x = y := eq_of_mabs_div_le_one <| le_of_forall_gt h

