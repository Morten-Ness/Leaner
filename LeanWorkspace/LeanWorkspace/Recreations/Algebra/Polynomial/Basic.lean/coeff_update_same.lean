import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_update_same (p : R[X]) (n : ℕ) (a : R) : (p.update n a).coeff n = a := by
  rw [Polynomial.coeff_update_apply p, if_pos rfl]

