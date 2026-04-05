import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem divX_C (a : R) : Polynomial.divX (Polynomial.C a) = 0 := ext fun n => by simp [Polynomial.coeff_divX]

