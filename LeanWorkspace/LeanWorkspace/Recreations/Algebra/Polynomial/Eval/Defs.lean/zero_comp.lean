import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem zero_comp : Polynomial.comp (0 : R[X]) p = 0 := by rw [← C_0, Polynomial.C_comp]

