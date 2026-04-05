import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_add_eq_right_of_lt (pn : p.natDegree < n) : (p + q).coeff n = q.coeff n := by
  rw [add_comm]
  exact Polynomial.coeff_add_eq_left_of_lt pn

