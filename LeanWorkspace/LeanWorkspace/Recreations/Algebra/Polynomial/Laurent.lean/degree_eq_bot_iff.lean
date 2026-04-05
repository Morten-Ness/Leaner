import Mathlib

open scoped LaurentPolynomial

variable {R S : Type*}

variable [Semiring R]

set_option backward.isDefEq.respectTransparency false in
theorem degree_eq_bot_iff {f : R[T;T⁻¹]} : f.degree = ⊥ ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, LaurentPolynomial.degree_zero]⟩
  ext n
  simp only [coe_zero, Pi.zero_apply]
  simp_rw [LaurentPolynomial.degree, Finset.max_eq_sup_withBot, Finset.sup_eq_bot_iff, Finsupp.mem_support_iff, Ne,
    WithBot.coe_ne_bot, imp_false, not_not] at h
  exact h n

