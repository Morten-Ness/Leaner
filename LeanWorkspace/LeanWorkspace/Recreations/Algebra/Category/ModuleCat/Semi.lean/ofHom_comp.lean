import Mathlib

variable (R : Type u) [Semiring R]

theorem ofHom_comp {M N O : Type v} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O] [Module R M]
    [Module R N] [Module R O] (f : M →ₗ[R] N) (g : N →ₗ[R] O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

