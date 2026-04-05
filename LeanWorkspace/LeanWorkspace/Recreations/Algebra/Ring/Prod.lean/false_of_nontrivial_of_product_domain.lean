import Mathlib

variable {R R' S S' T : Type*}

theorem false_of_nontrivial_of_product_domain (R S : Type*) [Semiring R] [Semiring S]
    [IsDomain (R × S)] [Nontrivial R] [Nontrivial S] : False := by
  have :=
    NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (show ((0 : R), (1 : S)) * (1, 0) = 0 by simp)
  rw [Prod.mk_eq_zero, Prod.mk_eq_zero] at this
  rcases this with (⟨_, h⟩ | ⟨h, _⟩)
  · exact zero_ne_one h.symm
  · exact zero_ne_one h.symm

