import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_eq_factorial_smul_sum (p : R[X]) (k : ℕ) :
    Polynomial.derivative^[k] p = k ! •
      ∑ x ∈ (Polynomial.derivative^[k] p).support, Polynomial.C ((x + k).choose k • p.coeff (x + k)) * Polynomial.X ^ x := by
  conv_lhs => rw [Polynomial.iterate_derivative_eq_sum]
  rw [smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← smul_mul_assoc, smul_C, smul_smul, Nat.descFactorial_eq_factorial_mul_choose]

