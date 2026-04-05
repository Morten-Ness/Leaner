import Mathlib

variable {R S : Type*}

variable [CommRing R]

theorem sub_dvd_pow_sub_pow (x y : R) (n : ℕ) : x - y ∣ x ^ n - y ^ n := (Commute.all x y).sub_dvd_pow_sub_pow n

