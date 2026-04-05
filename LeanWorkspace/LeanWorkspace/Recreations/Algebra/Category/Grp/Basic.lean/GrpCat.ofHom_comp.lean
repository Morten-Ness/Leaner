import Mathlib

theorem ofHom_comp {X Y Z : Type u} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

