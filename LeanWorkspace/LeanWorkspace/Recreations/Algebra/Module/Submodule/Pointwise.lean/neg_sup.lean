import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem neg_sup (S T : Submodule R M) : -(S ⊔ T) = -S ⊔ -T := (Submodule.negOrderIso : Submodule R M ≃o Submodule R M).map_sup S T

