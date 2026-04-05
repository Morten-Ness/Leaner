import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem degree_derivative_le {p : R[X]} : p.derivative.degree ≤ p.degree := letI := Classical.decEq R
  if H : p = 0 then le_of_eq <| by rw [H, Polynomial.derivative_zero] else (Polynomial.degree_derivative_lt H).le

