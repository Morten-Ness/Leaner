import Mathlib

variable {R : Type u} [CommSemiring R]

theorem hom_whiskerRight {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R) :
    (f ▷ N).hom = f.hom.rTensor N := rfl

