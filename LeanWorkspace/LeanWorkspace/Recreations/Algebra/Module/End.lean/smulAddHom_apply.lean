import Mathlib

variable {R S M M₂ : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

theorem smulAddHom_apply : smulAddHom R M r x = r • x := rfl

