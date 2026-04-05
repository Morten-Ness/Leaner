import Mathlib

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem ncoeff_apply (A : VertexOperator R V) (n : ℤ) : VertexOperator.ncoeff A n = coeff A (-n - 1) := rfl

