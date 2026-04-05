import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

theorem induction_on' {motive : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (C_mul_T : ∀ (n : ℤ) (a : R), motive (Polynomial.C a * LaurentPolynomial.T n)) : motive p := by
  refine LaurentPolynomial.induction_on p (fun a => ?_) (fun {p q} => add p q) ?_ ?_ <;>
      try exact fun n f _ => C_mul_T _ f
  convert C_mul_T 0 a
  exact (mul_one _).symm

