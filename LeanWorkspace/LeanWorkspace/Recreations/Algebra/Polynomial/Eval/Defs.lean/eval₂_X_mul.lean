import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

variable [Semiring T]

theorem eval₂_X_mul : eval₂ f x (Polynomial.X * p) = eval₂ f x p * x := by rw [X_mul, Polynomial.eval₂_mul_X]

