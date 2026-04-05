import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem divX_C_mul : Polynomial.divX (Polynomial.C a * p) = Polynomial.C a * Polynomial.divX p := by
  ext
  simp

