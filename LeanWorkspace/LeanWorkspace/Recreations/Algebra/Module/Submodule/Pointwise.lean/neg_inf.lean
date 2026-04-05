import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem neg_inf (S T : Submodule R M) : -(S ⊓ T) = -S ⊓ -T := rfl

