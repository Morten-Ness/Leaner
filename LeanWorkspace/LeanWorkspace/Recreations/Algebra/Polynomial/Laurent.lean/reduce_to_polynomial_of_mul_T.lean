import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem reduce_to_polynomial_of_mul_T (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
    (Qf : ∀ f : R[X], Q (toLaurent f)) (QT : ∀ f, Q (f * LaurentPolynomial.T 1) → Q f) : Q f := by
  induction f using LaurentPolynomial.induction_on_mul_T with | _ f n
  induction n with
  | zero => simpa only [Nat.cast_zero, neg_zero, LaurentPolynomial.T_zero, mul_one] using Qf _
  | succ n hn => convert QT _ _; simpa using hn

