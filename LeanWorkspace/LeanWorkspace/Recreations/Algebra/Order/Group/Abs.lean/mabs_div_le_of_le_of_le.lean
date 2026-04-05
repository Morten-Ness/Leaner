import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_le_of_le_of_le {a b lb ub : G} (hal : lb ≤ a) (hau : a ≤ ub) (hbl : lb ≤ b)
    (hbu : b ≤ ub) : |a / b|ₘ ≤ ub / lb := mabs_div_le_iff.2 ⟨div_le_div'' hau hbl, div_le_div'' hbu hal⟩

