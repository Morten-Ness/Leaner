import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem mem_support_derivative [IsAddTorsionFree R] (p : R[X]) (n : ℕ) :
    n ∈ (Polynomial.derivative p).support ↔ n + 1 ∈ p.support := by
  suffices ¬p.coeff (n + 1) * (n + 1 : ℕ) = 0 ↔ coeff p (n + 1) ≠ 0 by
    simpa only [mem_support_iff, Polynomial.coeff_derivative, Ne, Nat.cast_succ]
  rw [← nsmul_eq_mul', smul_eq_zero]
  simp only [Nat.succ_ne_zero, false_or]

