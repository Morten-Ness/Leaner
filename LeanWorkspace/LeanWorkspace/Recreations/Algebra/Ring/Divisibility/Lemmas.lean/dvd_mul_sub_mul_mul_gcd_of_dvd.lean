import Mathlib

variable {R : Type*}

variable [CommRing R]

theorem dvd_mul_sub_mul_mul_gcd_of_dvd {p a b c d x y : R} [GCDMonoid R]
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * gcd x y := by
  rw [← (gcd_mul_left' (a * d - b * c) x y).dvd_iff_dvd_right]
  exact (dvd_gcd_iff _ _ _).2 ⟨dvd_mul_sub_mul_mul_left_of_dvd h1 h2,
    dvd_mul_sub_mul_mul_right_of_dvd h1 h2⟩

