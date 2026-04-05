import Mathlib

variable {R S : CommRingCat.{u}}

theorem toUnder_hom_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (a : A) :
    f.toUnder.hom.right a = f a := rfl

