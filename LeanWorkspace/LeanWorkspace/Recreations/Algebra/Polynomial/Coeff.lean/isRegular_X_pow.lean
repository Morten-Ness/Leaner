import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem isRegular_X_pow (n : ℕ) : IsRegular (Polynomial.X ^ n : R[X]) := by
  suffices IsLeftRegular (Polynomial.X ^ n : R[X]) from
    ⟨this, this.right_of_commute (fun p => commute_X_pow p n)⟩
  intro P Q (hPQ : Polynomial.X ^ n * P = Polynomial.X ^ n * Q)
  ext i
  rw [← Polynomial.coeff_X_pow_mul P n i, hPQ, Polynomial.coeff_X_pow_mul Q n i]

