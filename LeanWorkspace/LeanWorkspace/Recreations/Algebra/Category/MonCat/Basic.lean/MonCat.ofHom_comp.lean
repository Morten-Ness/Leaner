import Mathlib

theorem ofHom_comp {M N P : Type u} [Monoid M] [Monoid N] [Monoid P]
    (f : M →* N) (g : N →* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

