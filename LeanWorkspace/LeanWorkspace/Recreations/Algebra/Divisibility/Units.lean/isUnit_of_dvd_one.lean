import Mathlib

variable {α : Type*}

variable [CommMonoid α]

theorem isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α) := isUnit_iff_dvd_one.mpr h

