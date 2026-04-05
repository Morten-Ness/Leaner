import Mathlib

variable {α : Type*}

variable [CommMonoid α]

theorem not_isUnit_of_not_isUnit_dvd {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b := mt (isUnit_of_dvd_unit hb) ha

