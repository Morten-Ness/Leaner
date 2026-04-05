import Mathlib

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

theorem taylor_pow (n : ℕ) : Polynomial.taylor r (f ^ n) = Polynomial.taylor r f ^ n := (Polynomial.taylorAlgHom r).map_pow ..

