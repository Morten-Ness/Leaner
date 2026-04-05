import Mathlib

variable (R : Type u) [CommRing R]

theorem hom_comp {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

