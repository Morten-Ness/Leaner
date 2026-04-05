import Mathlib

variable {R : Type u} [CommRing R]

theorem hom_whiskerRight {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R) :
    (f ▷ N).hom = f.hom.rTensor N := rfl

