import Mathlib

variable (R : Type u) [Ring R]

theorem ofHom_comp {M N O : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup O] [Module R M]
    [Module R N] [Module R O] (f : M →ₗ[R] N) (g : N →ₗ[R] O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

