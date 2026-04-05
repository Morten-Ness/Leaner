import Mathlib

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A]

variable [StarMul A] [Algebra R A] [StarModule R A]

theorem algebraMap_star_comm (r : R) : algebraMap R A (star r) = star (algebraMap R A r) := by
  simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]

