import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

theorem eq_bot_of_subsingleton [Subsingleton p] : p = ⊥ := Submodule.subsingleton_iff_eq_bot.mp inferInstance

