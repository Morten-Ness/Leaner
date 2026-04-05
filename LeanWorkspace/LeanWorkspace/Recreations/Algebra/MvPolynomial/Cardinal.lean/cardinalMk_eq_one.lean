import Mathlib

variable {σ : Type u} {R : Type v} [CommSemiring R]

theorem cardinalMk_eq_one [Subsingleton R] : #(MvPolynomial σ R) = 1 := mk_eq_one _

