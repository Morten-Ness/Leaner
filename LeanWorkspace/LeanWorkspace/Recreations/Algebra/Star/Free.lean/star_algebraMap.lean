import Mathlib

variable {R : Type*} [CommSemiring R] {X : Type*}

theorem star_algebraMap (r : R) : star (algebraMap R (FreeAlgebra R X) r) = algebraMap R _ r := by
  simp [star, Star.star]

