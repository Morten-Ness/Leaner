import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q ≠ 0) : p.natDegree ≤ q.natDegree := by
  obtain ⟨q, rfl⟩ := h1
  rw [mul_ne_zero_iff] at h2
  rw [Polynomial.natDegree_mul h2.1 h2.2]; exact Nat.le_add_right _ _

