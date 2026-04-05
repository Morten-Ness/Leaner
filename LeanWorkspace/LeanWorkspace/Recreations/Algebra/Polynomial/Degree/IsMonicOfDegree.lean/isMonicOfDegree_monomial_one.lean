import Mathlib

variable {R : Type*}

variable [Semiring R]

variable [Nontrivial R]

theorem isMonicOfDegree_monomial_one (n : ℕ) : IsMonicOfDegree (monomial n (1 : R)) n := by
  simpa only [monomial_one_right_eq_X_pow] using Polynomial.isMonicOfDegree_X_pow R n

