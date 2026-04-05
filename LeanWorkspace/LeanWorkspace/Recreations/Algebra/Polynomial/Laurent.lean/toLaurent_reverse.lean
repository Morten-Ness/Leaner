import Mathlib

open scoped Polynomial

variable {R S : Type*}

variable {R : Type*} [CommSemiring R]

theorem toLaurent_reverse (p : R[X]) :
    toLaurent p.reverse = LaurentPolynomial.invert (toLaurent p) * (LaurentPolynomial.T p.natDegree) := by
  nontriviality R
  induction p using Polynomial.recOnHorner with
  | M0 => simp
  | MC _ _ _ _ ih => simp [add_mul, ← ih]
  | MX _ hp => simpa [natDegree_mul_X hp]

