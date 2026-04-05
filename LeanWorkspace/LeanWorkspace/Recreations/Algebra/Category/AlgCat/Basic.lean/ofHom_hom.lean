import Mathlib

variable (R : Type u) [CommRing R]

theorem ofHom_hom {A B : AlgCat.{v} R} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

