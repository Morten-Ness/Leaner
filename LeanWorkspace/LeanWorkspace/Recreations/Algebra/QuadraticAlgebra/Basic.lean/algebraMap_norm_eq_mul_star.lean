import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem algebraMap_norm_eq_mul_star (z : QuadraticAlgebra R a b) :
    (algebraMap R _ (QuadraticAlgebra.norm z : R)) = z * star z := by
  ext <;> simp [QuadraticAlgebra.norm, star, mul_comm] <;> ring

