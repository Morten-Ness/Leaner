import Mathlib

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : n < HahnSeries.order ((HahnModule.of R).symm (A x))) : coeff A n x = 0 := by
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  lia

