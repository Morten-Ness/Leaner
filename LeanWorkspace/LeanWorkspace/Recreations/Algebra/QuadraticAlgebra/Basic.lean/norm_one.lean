import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_one : QuadraticAlgebra.norm (1 : QuadraticAlgebra R a b) = 1 := by simp [QuadraticAlgebra.norm]

