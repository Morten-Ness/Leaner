import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [CommSemiring R]

theorem smul_C (r1 r2 : R) :
    r1 • (.C r2 : QuadraticAlgebra R a b) = .C (r1 * r2) := by rw [QuadraticAlgebra.C_mul, QuadraticAlgebra.C_mul_eq_smul]

