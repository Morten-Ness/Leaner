import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem neg_eq_self_iff_neg_le {S : Submodule R M} : -S = S ↔ -S ≤ S := ⟨le_of_eq, fun h => antisymm h <| Submodule.neg_le.mp h⟩

