import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

omit [IsOrderedMonoid G] in
theorem min_mabs_mabs_le_mabs_max : min |a|ₘ |b|ₘ ≤ |max a b|ₘ := (le_total a b).elim (fun h => (min_le_right _ _).trans_eq <| congr_arg _ (max_eq_right h).symm)
    fun h => (min_le_left _ _).trans_eq <| congr_arg _ (max_eq_left h).symm

