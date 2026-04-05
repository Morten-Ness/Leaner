import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.aveal_eq_map_swap (x : A) (p : R[X][Y]) :
    aeval (C x) p = mapAlgHom (aeval x) (swap p) := by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
      simp
      induction a using Polynomial.induction_on'
        <;> aesop (add norm [add_mul, C_mul_X_pow_eq_monomial])

