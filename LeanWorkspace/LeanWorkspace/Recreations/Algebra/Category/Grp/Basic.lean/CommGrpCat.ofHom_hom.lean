import Mathlib

theorem ofHom_hom {X Y : CommGrpCat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

