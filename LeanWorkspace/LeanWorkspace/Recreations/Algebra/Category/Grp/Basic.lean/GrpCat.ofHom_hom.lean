import Mathlib

theorem ofHom_hom {X Y : GrpCat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

