import Mathlib

theorem ofHom_comp {M N P : Type u} [Mul M] [Mul N] [Mul P]
    (f : M →ₙ* N) (g : N →ₙ* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

