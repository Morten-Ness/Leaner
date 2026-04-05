import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.aevalAeval_swap (x y : A) (p : R[X][Y]) :
    aevalAeval x y (swap p) = aevalAeval y x p := by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
    simp
    induction a using Polynomial.induction_on' <;> aesop (add norm add_mul)

attribute [local instance] Polynomial.algebra in

