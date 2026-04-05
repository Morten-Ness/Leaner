import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [NonUnitalNonAssocSemiring R]

theorem C_mul (x y : R) : .C (x * y) = (.C x * .C y : QuadraticAlgebra R a b) := by
  ext <;> simp

