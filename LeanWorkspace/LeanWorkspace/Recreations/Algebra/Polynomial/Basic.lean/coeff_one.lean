import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_one {n : ℕ} : Polynomial.coeff (1 : R[X]) n = if n = 0 then 1 else 0 := by
  simp_rw [eq_comm (a := n) (b := 0)]
  exact Polynomial.coeff_monomial

