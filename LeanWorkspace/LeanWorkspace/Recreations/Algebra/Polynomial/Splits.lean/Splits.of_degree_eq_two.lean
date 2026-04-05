import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.of_degree_eq_two {x : R} (h₁ : f.degree = 2) (h₂ : f.eval x = 0) : Polynomial.Splits f := Polynomial.Splits.of_natDegree_eq_two (natDegree_eq_of_degree_eq_some h₁) h₂

