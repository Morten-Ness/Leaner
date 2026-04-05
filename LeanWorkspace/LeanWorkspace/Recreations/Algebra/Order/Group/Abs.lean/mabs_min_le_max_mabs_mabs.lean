import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

omit [IsOrderedMonoid G] in
theorem mabs_min_le_max_mabs_mabs : |min a b|ₘ ≤ max |a|ₘ |b|ₘ := (le_total a b).elim (fun h => (congr_arg _ <| min_eq_left h).trans_le <| le_max_left _ _) fun h =>
    (congr_arg _ <| min_eq_right h).trans_le <| le_max_right _ _

