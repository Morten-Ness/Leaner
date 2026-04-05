import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_intCast (n : ℤ) : QuadraticAlgebra.norm (n : QuadraticAlgebra R a b) = n ^ 2 := by
  simp [QuadraticAlgebra.norm_def, pow_two]

