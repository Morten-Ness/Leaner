import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem comp_C_mul_X_eq_zero_iff {r : R} (hr : r ∈ nonZeroDivisors R) :
    p.comp (Polynomial.C r * Polynomial.X) = 0 ↔ p = 0 := by
  simp_rw [ext_iff]
  refine forall_congr' fun n ↦ ?_
  rw [comp_C_mul_X_coeff, coeff_zero, mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hr _)]

