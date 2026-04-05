import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem leftInverse_trunc_toLaurent :
    Function.LeftInverse (LaurentPolynomial.trunc : R[T;T⁻¹] → R[X]) Polynomial.toLaurent := by
  refine fun f => LaurentPolynomial.induction_on' f ?_ ?_
  · intro f g hf hg
    simp only [hf, hg, map_add]
  · intro n r
    simp only [Polynomial.toLaurent_C_mul_T, LaurentPolynomial.trunc_C_mul_T, Int.natCast_nonneg, Int.toNat_natCast,
      if_true]

