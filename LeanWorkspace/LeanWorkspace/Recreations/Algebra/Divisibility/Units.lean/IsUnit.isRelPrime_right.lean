import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsUnit.isRelPrime_right (h : IsUnit y) : IsRelPrime x y := h.isRelPrime_left.symm

