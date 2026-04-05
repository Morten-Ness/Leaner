import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_C : Polynomial.coeff (Polynomial.C a) n = ite (n = 0) a 0 := by
  convert Polynomial.coeff_monomial (a := a) (m := n) (n := 0) using 2
  simp [eq_comm]

