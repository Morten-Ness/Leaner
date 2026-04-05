import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem coe_set_neg (S : Submodule R M) : ↑(-S) = -(S : Set M) := rfl

