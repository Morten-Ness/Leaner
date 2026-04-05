import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem IsUnit.isRelPrime_left (h : IsUnit x) : IsRelPrime x y := fun _ hx _ ↦ isUnit_of_dvd_unit hx h

