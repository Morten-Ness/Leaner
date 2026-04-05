import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_eq_sum (p : R[X]) (k : ℕ) :
    Polynomial.derivative^[k] p =
      ∑ x ∈ (Polynomial.derivative^[k] p).support, Polynomial.C ((x + k).descFactorial k • p.coeff (x + k)) * Polynomial.X ^ x := by
  conv_lhs => rw [(Polynomial.derivative^[k] p).as_sum_support_C_mul_X_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.coeff_iterate_derivative, Nat.descFactorial_eq_factorial_mul_choose]

