import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem self_sub_monomial_natDegree_leadingCoeff {R : Type*} [Ring R] (f : R[X]) :
    f - monomial f.natDegree f.leadingCoeff = f.eraseLead := (eq_sub_iff_add_eq.mpr (Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff f)).symm

