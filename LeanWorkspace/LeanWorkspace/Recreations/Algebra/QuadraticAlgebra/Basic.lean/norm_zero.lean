import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_zero : QuadraticAlgebra.norm (0 : QuadraticAlgebra R a b) = 0 := by simp [QuadraticAlgebra.norm]

