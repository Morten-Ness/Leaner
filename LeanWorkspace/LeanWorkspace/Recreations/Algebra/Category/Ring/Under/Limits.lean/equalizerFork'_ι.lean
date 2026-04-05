import Mathlib

variable {R S : CommRingCat.{u}}

variable [Algebra R S]

theorem equalizerFork'_ι {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A →ₐ[R] B) :
    (CommRingCat.Under.equalizerFork' f g).ι = (AlgHom.equalizer f g).val.toUnder := rfl

