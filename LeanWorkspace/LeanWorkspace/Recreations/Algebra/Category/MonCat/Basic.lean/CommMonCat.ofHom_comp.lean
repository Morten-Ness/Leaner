import Mathlib

theorem ofHom_comp {M N P : Type u} [CommMonoid M] [CommMonoid N] [CommMonoid P]
    (f : M →* N) (g : N →* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

