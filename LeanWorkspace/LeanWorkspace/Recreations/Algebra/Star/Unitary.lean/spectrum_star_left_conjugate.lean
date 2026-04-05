import Mathlib

variable {R : Type*}

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] [StarMul A]

theorem spectrum_star_left_conjugate {a : A} {U : unitary A} :
    spectrum R ((star U : A) * a * U) = spectrum R a := by
  simpa using Unitary.spectrum_star_right_conjugate (U := star U)

