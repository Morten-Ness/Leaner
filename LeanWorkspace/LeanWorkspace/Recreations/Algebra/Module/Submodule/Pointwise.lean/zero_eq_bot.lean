import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem zero_eq_bot : (0 : Submodule R M) = ⊥ := rfl

