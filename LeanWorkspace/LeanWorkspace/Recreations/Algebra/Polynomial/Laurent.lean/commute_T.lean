import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem commute_T (n : ℤ) (f : R[T;T⁻¹]) : Commute (LaurentPolynomial.T n) f := LaurentPolynomial.induction_on' f (fun _ _ Tp Tq => Commute.add_right Tp Tq) fun m a =>
    show LaurentPolynomial.T n * _ = _ by
      rw [LaurentPolynomial.T, LaurentPolynomial.T, ← LaurentPolynomial.single_eq_C, single_mul_single, single_mul_single, single_mul_single]
      simp [add_comm]

