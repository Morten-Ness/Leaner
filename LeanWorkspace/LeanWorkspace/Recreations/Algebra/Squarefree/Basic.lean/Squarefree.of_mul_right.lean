import Mathlib

variable {R : Type*}

theorem Squarefree.of_mul_right [CommMonoid R] {m n : R} (hmn : Squarefree (m * n)) :
    Squarefree n := fun p hp => hmn p (dvd_mul_of_dvd_right hp m)

