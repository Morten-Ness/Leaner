import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem isRelPrime_one_left : IsRelPrime 1 x := isUnit_one.isRelPrime_left

