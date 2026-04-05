import Mathlib

variable {R : Type*}

variable [CommRing R]

theorem dvd_mul_sub_mul_mul_right_of_dvd {p a b c d x y : R}
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * y := (mul_comm a _ ▸ mul_comm c _ ▸ dvd_mul_sub_mul_mul_left_of_dvd
    (add_comm (c * x) _ ▸ h2) (add_comm (a * x) _ ▸ h1))

