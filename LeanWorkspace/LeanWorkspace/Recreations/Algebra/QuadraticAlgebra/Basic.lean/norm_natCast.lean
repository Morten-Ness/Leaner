import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_natCast (n : ℕ) : QuadraticAlgebra.norm (n : QuadraticAlgebra R a b) = n ^ 2 := by
  simp [QuadraticAlgebra.norm_def, pow_two]

