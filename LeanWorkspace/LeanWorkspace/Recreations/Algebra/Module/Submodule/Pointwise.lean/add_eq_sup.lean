import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem add_eq_sup (p q : Submodule R M) : p + q = p ⊔ q := rfl

