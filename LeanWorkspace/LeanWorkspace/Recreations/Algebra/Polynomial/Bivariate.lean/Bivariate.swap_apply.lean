import Mathlib

open scoped Polynomial.Bivariate

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem Bivariate.swap_apply (p : R[X][Y]) : swap p = p.aevalAeval (A := R[X][Y]) Y (C X) := rfl

attribute [local simp] Bivariate.swap_apply

