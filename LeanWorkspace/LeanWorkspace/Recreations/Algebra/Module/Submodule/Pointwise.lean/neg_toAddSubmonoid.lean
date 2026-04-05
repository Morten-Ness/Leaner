import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem neg_toAddSubmonoid (S : Submodule R M) : (-S).toAddSubmonoid = -S.toAddSubmonoid := rfl

