import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

omit [IsOrderedMonoid G] in
theorem mabs_max_le_max_mabs_mabs : |max a b|ₘ ≤ max |a|ₘ |b|ₘ := (le_total a b).elim (fun h => (congr_arg _ <| max_eq_right h).trans_le <| le_max_right _ _)
    fun h => (congr_arg _ <| max_eq_left h).trans_le <| le_max_left _ _

