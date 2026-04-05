import Mathlib

variable {R S : CommRingCat.{u}}

variable [Algebra R S]

theorem equalizerFork_ι {A B : CommRingCat.Under R} (f g : A ⟶ B) :
    (CommRingCat.Under.equalizerFork f g).ι = (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder := rfl

