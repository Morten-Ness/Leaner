import Mathlib

theorem ofHom_hom {M N : MonCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

