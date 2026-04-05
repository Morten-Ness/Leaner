import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem exists_T_pow (f : R[T;T⁻¹]) : ∃ (n : ℕ) (f' : R[X]), toLaurent f' = f * LaurentPolynomial.T n := by
  refine LaurentPolynomial.induction_on' f ?_ fun n a => ?_ <;> clear f
  · rintro f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩
    refine ⟨m + n, fn * Polynomial.X ^ n + gn * Polynomial.X ^ m, ?_⟩
    simp only [hf, hg, add_mul, add_comm (n : ℤ), map_add, map_mul, Polynomial.toLaurent_X_pow,
      LaurentPolynomial.mul_T_assoc, Int.natCast_add]
  · rcases n with n | n
    · exact ⟨0, Polynomial.C a * Polynomial.X ^ n, by simp⟩
    · refine ⟨n + 1, Polynomial.C a, ?_⟩
      simp only [Int.negSucc_eq, Polynomial.toLaurent_C, Int.natCast_succ, LaurentPolynomial.mul_T_assoc,
        neg_add_cancel, LaurentPolynomial.T_zero, mul_one]

