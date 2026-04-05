import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem single_eq_C_mul_T (r : R) (n : ℤ) : .single n r = Polynomial.C r * LaurentPolynomial.T n := by
  simp [Polynomial.C, LaurentPolynomial.T, single_mul_single]

-- This lemma locks in the right changes and is what Lean proved directly.
-- The actual `simp`-normal form of a Laurent monomial is `Polynomial.C a * LaurentPolynomial.T n`, whenever it can be reached.

