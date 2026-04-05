import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem bot_toAddSubmonoid : (⊥ : Submodule R M).toAddSubmonoid = ⊥ := rfl

