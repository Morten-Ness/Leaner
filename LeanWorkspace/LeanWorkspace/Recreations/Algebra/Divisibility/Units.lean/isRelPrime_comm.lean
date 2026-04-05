import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x := ⟨IsRelPrime.symm, IsRelPrime.symm⟩

