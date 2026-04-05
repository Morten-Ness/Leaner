import Mathlib

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

theorem taylor_mul (p q : R[X]) : Polynomial.taylor r (p * q) = Polynomial.taylor r p * Polynomial.taylor r q := mul_comp ..

