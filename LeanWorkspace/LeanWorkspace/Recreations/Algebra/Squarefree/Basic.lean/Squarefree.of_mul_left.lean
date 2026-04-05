import Mathlib

variable {R : Type*}

theorem Squarefree.of_mul_left [Monoid R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree m := fun p hp => hmn p (dvd_mul_of_dvd_left hp n)

