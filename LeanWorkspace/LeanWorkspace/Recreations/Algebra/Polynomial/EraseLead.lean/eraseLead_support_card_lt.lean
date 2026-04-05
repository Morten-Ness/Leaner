import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_support_card_lt (h : f ≠ 0) : #(Polynomial.eraseLead f).support < #f.support := by
  rw [Polynomial.eraseLead_support]
  exact card_lt_card (erase_ssubset <| natDegree_mem_support_of_nonzero h)

