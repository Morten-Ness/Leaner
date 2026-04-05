import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem isRelPrime_one_right : IsRelPrime x 1 := isUnit_one.isRelPrime_right

