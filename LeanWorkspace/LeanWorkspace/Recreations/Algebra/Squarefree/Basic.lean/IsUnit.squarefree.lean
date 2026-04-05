import Mathlib

variable {R : Type*}

theorem IsUnit.squarefree [CommMonoid R] {x : R} (h : IsUnit x) : Squarefree x := fun _ hdvd =>
  isUnit_of_mul_isUnit_left (isUnit_of_dvd_unit hdvd h)

