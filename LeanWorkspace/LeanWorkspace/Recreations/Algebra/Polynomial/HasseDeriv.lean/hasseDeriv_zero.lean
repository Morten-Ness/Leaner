import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_zero : @Polynomial.hasseDeriv R _ 0 = LinearMap.id := LinearMap.ext <| Polynomial.hasseDeriv_zero'

