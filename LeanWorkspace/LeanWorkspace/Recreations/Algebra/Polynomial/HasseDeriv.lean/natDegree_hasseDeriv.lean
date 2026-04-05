import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem natDegree_hasseDeriv [IsAddTorsionFree R] (p : R[X]) (n : ℕ) :
    natDegree (Polynomial.hasseDeriv n p) = natDegree p - n := by
  classical
  refine map_natDegree_eq_sub (fun h => Polynomial.hasseDeriv_eq_zero_of_lt_natDegree _ _) ?_
  simp only [Ne, Polynomial.hasseDeriv_monomial, natDegree_monomial, ite_eq_right_iff]
  simp +contextual [← nsmul_eq_mul, Nat.choose_eq_zero_iff, le_of_lt]

