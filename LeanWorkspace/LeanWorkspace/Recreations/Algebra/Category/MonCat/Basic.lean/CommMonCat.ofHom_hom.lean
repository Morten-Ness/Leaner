import Mathlib

theorem ofHom_hom {M N : CommMonCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

