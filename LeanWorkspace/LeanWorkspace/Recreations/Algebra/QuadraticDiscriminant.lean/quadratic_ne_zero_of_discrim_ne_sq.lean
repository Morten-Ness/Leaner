import Mathlib

variable {R : Type*}

variable [CommRing R] {a b c : R}

theorem quadratic_ne_zero_of_discrim_ne_sq (h : ∀ s : R, discrim a b c ≠ s ^ 2) (x : R) :
    a * (x * x) + b * x + c ≠ 0 := mt discrim_eq_sq_of_quadratic_eq_zero (h _)

