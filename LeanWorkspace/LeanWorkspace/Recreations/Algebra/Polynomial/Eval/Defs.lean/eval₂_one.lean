import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

theorem eval₂_one : (1 : R[X]).eval₂ f x = 1 := by rw [← C_1, Polynomial.eval₂_C, f.map_one]

