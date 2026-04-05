import Mathlib

variable {ι M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R] (s : Multiset R)

theorem multiset_sum_right (a : R) (h : ∀ b ∈ s, Commute a b) : Commute a s.sum := by
  induction s using Quotient.inductionOn
  rw [quot_mk_to_coe, sum_coe]
  exact Commute.list_sum_right _ _ h

