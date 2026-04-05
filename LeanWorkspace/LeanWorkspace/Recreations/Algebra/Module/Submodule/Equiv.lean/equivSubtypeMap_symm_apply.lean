import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {N : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

theorem equivSubtypeMap_symm_apply {p : Submodule R M} {q : Submodule R p} (x : q.map p.subtype) :
    ((p.equivSubtypeMap q).symm x : M) = x := rfl

