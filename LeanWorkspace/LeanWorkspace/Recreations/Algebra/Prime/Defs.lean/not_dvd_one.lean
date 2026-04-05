import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

variable {p : M} (hp : Prime p)

theorem not_dvd_one : ¬p ∣ 1 := mt (isUnit_of_dvd_one ·) Prime.not_unit hp

