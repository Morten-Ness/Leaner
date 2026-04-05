import Mathlib

open scoped Polynomial

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

variable {R : Type*} [CommRing R]

theorem Polynomial.fwdDiff_iter_degree_add_one_eq_zero (P : R[X]) :
    Δ_[1]^[P.natDegree + 1] P.eval = 0 := by
  have hP : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self P.natDegree
  exact Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP

