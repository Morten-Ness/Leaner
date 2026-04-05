import Mathlib

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p p' : Submodule R M}

theorem coe_inclusion (h : p ≤ p') (x : p) : (Submodule.inclusion h x : M) = x := rfl

