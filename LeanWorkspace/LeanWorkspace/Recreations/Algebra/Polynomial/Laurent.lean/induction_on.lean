import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
theorem induction_on {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹]) (h_C : ∀ a, M (Polynomial.C a))
    (h_add : ∀ {p q}, M p → M q → M (p + q))
    (h_C_mul_T : ∀ (n : ℕ) (a : R), M (Polynomial.C a * LaurentPolynomial.T n) → M (Polynomial.C a * LaurentPolynomial.T (n + 1)))
    (h_C_mul_T_Z : ∀ (n : ℕ) (a : R), M (Polynomial.C a * LaurentPolynomial.T (-n)) → M (Polynomial.C a * LaurentPolynomial.T (-n - 1))) : M p := by
  have A : ∀ {n : ℤ} {a : R}, M (Polynomial.C a * LaurentPolynomial.T n) := by
    intro n a
    refine Int.induction_on n ?_ ?_ ?_
    · simpa only [LaurentPolynomial.T_zero, mul_one] using h_C a
    · exact fun m => h_C_mul_T m a
    · exact fun m => h_C_mul_T_Z m a
  have B : ∀ s : Finset ℤ, M (s.sum fun n : ℤ => Polynomial.C (p n) * LaurentPolynomial.T n) := by
    apply Finset.induction
    · convert h_C 0
      simp only [Finset.sum_empty, map_zero]
    · intro n s ns ih
      rw [Finset.sum_insert ns]
      exact h_add A ih
  convert B p.support
  ext a
  simp_rw [← LaurentPolynomial.single_eq_C_mul_T]
  rw [Finset.sum_apply', Finset.sum_eq_single a, single_eq_same]
  · intro b _ hb
    rw [single_eq_of_ne' hb]
  · intro ha
    rw [single_eq_same, notMem_support_iff.mp ha]

