import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem span_neg_eq_neg (s : Set M) : span R (-s) = -span R s := by
  apply le_antisymm
  · rw [span_le, Submodule.coe_set_neg, ← Set.neg_subset, neg_neg]
    exact subset_span
  · rw [Submodule.neg_le, span_le, Submodule.coe_set_neg, ← Set.neg_subset]
    exact subset_span

