import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hom_whiskerLeft (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L := rfl

