import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_divX : (Polynomial.divX p).coeff n = p.coeff (n + 1) := by
  rw [add_comm]; cases p; rfl

