import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_eraseLead_add_one (h : f ≠ 0) : #f.eraseLead.support + 1 = #f.support := by
  set c := #f.support with hc
  cases h₁ : c
  case zero =>
    by_contra
    exact h (card_support_eq_zero.mp h₁)
  case succ =>
    rw [Polynomial.eraseLead_support, card_erase_of_mem (natDegree_mem_support_of_nonzero h), ← hc, h₁]
    rfl

