import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable {x y : α}

theorem IsRelPrime.ne_zero_or_ne_zero [Nontrivial α] (h : IsRelPrime x y) : x ≠ 0 ∨ y ≠ 0 := not_or_of_imp <| by rintro rfl rfl; exact not_isRelPrime_zero_zero h

