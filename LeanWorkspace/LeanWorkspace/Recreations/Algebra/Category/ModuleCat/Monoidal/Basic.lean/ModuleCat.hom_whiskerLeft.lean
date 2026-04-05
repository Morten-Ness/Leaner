import Mathlib

variable {R : Type u} [CommRing R]

theorem hom_whiskerLeft (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L := rfl

