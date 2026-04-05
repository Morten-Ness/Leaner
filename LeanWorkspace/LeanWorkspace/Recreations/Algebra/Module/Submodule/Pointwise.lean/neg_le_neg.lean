import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem neg_le_neg {S T : Submodule R M} : -S ≤ -T ↔ S ≤ T := SetLike.coe_subset_coe.symm.trans Set.neg_subset_neg

