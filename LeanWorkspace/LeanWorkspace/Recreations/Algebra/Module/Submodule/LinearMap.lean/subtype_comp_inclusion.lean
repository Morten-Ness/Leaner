import Mathlib

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p p' : Submodule R M}

theorem subtype_comp_inclusion (p q : Submodule R M) (h : p ≤ q) :
    q.subtype.comp (Submodule.inclusion h) = p.subtype := rfl

