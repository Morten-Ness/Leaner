import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem one_comp : Polynomial.comp (1 : R[X]) p = 1 := by rw [← C_1, Polynomial.C_comp]

