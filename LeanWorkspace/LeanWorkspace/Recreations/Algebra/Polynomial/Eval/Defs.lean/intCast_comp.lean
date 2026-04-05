import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem intCast_comp (i : ℤ) : Polynomial.comp (i : R[X]) p = i := by cases i <;> simp

