import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_add_monomial_natDegree_leadingCoeff (f : R[X]) :
    f.eraseLead + monomial f.natDegree f.leadingCoeff = f := (add_comm _ _).trans (f.monomial_add_erase _)

