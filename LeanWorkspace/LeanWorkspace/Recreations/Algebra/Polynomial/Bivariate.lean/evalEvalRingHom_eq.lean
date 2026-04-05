import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R]

theorem evalEvalRingHom_eq (x : R) : evalEvalRingHom x = eval₂RingHom (evalRingHom x) := by
  ext <;> simp

