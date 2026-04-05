import Mathlib

theorem ofHom_comp {X Y Z : Type u} [Semigroup X] [Semigroup Y] [Semigroup Z]
    (f : X →ₙ* Y) (g : Y →ₙ* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

