import Mathlib

variable {R : Type*}

theorem dvd_zsmul_of_dvd [NonUnitalRing R] {x y : R} (z : ℤ) (h : x ∣ y) : x ∣ z • y := dvd_smul_of_dvd z h

