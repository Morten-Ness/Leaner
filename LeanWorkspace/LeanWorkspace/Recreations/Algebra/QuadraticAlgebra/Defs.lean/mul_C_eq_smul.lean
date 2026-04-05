import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [CommSemiring R]

theorem mul_C_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (x * .C r : QuadraticAlgebra R a b) = r • x := by
  rw [mul_comm, QuadraticAlgebra.C_mul_eq_smul r x]

