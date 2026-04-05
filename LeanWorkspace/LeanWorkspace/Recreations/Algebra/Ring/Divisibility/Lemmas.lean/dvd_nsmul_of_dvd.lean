import Mathlib

variable {R : Type*}

theorem dvd_nsmul_of_dvd [NonUnitalSemiring R] {x y : R} (n : ℕ) (h : x ∣ y) : x ∣ n • y := dvd_smul_of_dvd n h

