import Mathlib

open scoped Polynomial LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem induction_on_mul_T {motive : R[T;T⁻¹] → Prop} (f : R[T;T⁻¹])
    (mul_T : ∀ (f : R[X]) (n : ℕ), motive (toLaurent f * LaurentPolynomial.T (-n))) : motive f := by
  rcases LaurentPolynomial.exists_T_pow f with ⟨n, f', hf⟩
  rw [← mul_one f, ← LaurentPolynomial.T_zero, ← Nat.cast_zero, ← Nat.sub_self n, Nat.cast_sub rfl.le, LaurentPolynomial.T_sub,
    ← mul_assoc, ← hf]
  exact mul_T ..

