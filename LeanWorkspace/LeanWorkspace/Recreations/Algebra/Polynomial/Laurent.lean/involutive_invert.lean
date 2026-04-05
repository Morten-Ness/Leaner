import Mathlib

variable {R S : Type*}

variable {R : Type*} [CommSemiring R]

theorem involutive_invert : Function.Involutive (LaurentPolynomial.invert (R := R)) := fun _ ↦ by ext; simp

