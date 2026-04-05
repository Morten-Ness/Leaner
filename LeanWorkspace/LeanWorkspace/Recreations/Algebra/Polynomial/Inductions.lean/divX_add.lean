import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem divX_add : Polynomial.divX (p + q) = Polynomial.divX p + Polynomial.divX q := ext <| by simp

