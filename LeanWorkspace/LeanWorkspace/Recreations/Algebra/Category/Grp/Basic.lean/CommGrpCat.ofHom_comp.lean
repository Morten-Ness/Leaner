import Mathlib

theorem ofHom_comp {X Y Z : Type u} [CommGroup X] [CommGroup Y] [CommGroup Z]
    (f : X →* Y) (g : Y →* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

