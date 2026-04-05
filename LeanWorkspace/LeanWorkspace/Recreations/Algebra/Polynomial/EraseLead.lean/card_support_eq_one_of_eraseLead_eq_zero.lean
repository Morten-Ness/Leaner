import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_eq_one_of_eraseLead_eq_zero (h₀ : f ≠ 0) (h₁ : f.eraseLead = 0) :
    #f.support = 1 := (card_support_eq_zero.mpr h₁ ▸ Polynomial.card_support_eraseLead_add_one h₀).symm

