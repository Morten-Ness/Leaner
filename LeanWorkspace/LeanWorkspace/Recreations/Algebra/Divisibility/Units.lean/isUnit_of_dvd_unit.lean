import Mathlib

variable {α : Type*}

variable [CommMonoid α]

theorem isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUnit y) : IsUnit x := isUnit_iff_dvd_one.2 <| xy.trans <| isUnit_iff_dvd_one.1 hu

