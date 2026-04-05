import Mathlib

theorem ofHom_hom {M N : MagmaCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

