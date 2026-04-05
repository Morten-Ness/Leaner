import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_eraseLead : #f.eraseLead.support = #f.support - 1 := by
  by_cases hf : f = 0
  · rw [hf, Polynomial.eraseLead_zero, support_zero, card_empty]
  · rw [← Polynomial.card_support_eraseLead_add_one hf, add_tsub_cancel_right]

