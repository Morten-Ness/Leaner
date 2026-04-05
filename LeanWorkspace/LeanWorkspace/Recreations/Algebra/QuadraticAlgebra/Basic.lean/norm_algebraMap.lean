import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_algebraMap (r : R) : QuadraticAlgebra.norm (algebraMap R (QuadraticAlgebra R a b) r) = r ^ 2 := by
  simp [QuadraticAlgebra.norm_def, pow_two]

