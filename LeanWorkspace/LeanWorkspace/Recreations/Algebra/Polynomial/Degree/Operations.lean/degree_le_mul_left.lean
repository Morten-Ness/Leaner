import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

variable [NoZeroDivisors R] {p q : R[X]}

theorem degree_le_mul_left (p : R[X]) (hq : q ≠ 0) : degree p ≤ degree (p * q) := by
  classical
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · rw [Polynomial.degree_mul, degree_eq_natDegree hp, degree_eq_natDegree hq]
    exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)

