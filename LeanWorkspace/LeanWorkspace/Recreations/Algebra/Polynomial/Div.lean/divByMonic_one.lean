import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem divByMonic_one (p : R[X]) : p /ₘ 1 = p := by
  conv_rhs => rw [← Polynomial.modByMonic_add_div p 1]; simp

