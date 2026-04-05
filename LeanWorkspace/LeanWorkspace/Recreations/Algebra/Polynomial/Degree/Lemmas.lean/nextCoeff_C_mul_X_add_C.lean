import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {a : R}

theorem nextCoeff_C_mul_X_add_C (ha : a ≠ 0) (c : R) : nextCoeff (Polynomial.C a * Polynomial.X + Polynomial.C c) = c := by
  rw [nextCoeff_of_natDegree_pos] <;> simp [ha]

