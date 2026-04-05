import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_one : @Polynomial.hasseDeriv R _ 1 = derivative := LinearMap.ext <| Polynomial.hasseDeriv_one'

