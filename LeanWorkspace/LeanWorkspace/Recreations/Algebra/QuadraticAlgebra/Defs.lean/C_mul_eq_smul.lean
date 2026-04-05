import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [NonUnitalNonAssocSemiring R]

theorem C_mul_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (.C r * x : QuadraticAlgebra R a b) = r • x := by
  ext <;> simp

