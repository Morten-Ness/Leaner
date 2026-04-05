import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_neg (x : QuadraticAlgebra R a b) : (-x).norm = x.norm := by
  simp [QuadraticAlgebra.norm]

