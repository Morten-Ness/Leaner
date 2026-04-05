import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.natDegree_eq_one_of_irreducible {f : R[X]} (hf : Polynomial.Splits f)
    (h : Irreducible f) : natDegree f = 1 := natDegree_eq_of_degree_eq_some (hf.degree_eq_one_of_irreducible h)

