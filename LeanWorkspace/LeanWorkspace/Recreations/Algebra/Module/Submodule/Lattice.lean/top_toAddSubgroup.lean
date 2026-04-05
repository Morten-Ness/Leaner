import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem top_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] :
    (⊤ : Submodule R M).toAddSubgroup = ⊤ := rfl

