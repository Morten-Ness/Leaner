import Mathlib

variable {R S : CommRingCat.{u}}

theorem toUnder_trans {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (f.trans g).toUnder = f.toUnder ≪≫ g.toUnder := rfl

