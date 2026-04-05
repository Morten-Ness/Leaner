import Mathlib

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p p' : Submodule R M}

theorem inclusion_apply (h : p ≤ p') (x : p) : Submodule.inclusion h x = ⟨x, h x.2⟩ := rfl

