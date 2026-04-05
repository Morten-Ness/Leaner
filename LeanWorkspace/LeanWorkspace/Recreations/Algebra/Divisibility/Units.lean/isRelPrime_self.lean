import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem isRelPrime_self : IsRelPrime x x ↔ IsUnit x := ⟨(· dvd_rfl dvd_rfl), fun hu _ _ IsUnit.dvd ↦ isUnit_of_dvd_unit IsUnit.dvd hu⟩

