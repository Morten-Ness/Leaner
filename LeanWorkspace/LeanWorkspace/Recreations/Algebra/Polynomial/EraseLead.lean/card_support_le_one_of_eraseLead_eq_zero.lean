import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_le_one_of_eraseLead_eq_zero (h : f.eraseLead = 0) : #f.support ≤ 1 := by
  by_cases hpz : f = 0
  case pos => simp [hpz]
  case neg => exact le_of_eq (Polynomial.card_support_eq_one_of_eraseLead_eq_zero hpz h)

