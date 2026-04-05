import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable {x y : α}

theorem isRelPrime_zero_left : IsRelPrime 0 x ↔ IsUnit x := ⟨(· (dvd_zero _) dvd_rfl), IsUnit.isRelPrime_right⟩

