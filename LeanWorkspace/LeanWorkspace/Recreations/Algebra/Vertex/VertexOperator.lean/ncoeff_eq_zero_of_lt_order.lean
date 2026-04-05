import Mathlib

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem ncoeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : -n - 1 < HahnSeries.order ((HahnModule.of R).symm (A x))) : (A[[n]]) x = 0 := by
  simp only [VertexOperator.ncoeff, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

