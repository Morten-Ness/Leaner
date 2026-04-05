import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem revAt_eq_self_of_lt {N i : ℕ} (h : N < i) : Polynomial.revAt N i = i := by simp [Polynomial.revAt, Nat.not_le.mpr h]

