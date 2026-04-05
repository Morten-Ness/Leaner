import Mathlib

variable {R S : CommRingCat.{u}}

theorem toUnder_right {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (a : A) :
    f.toUnder.right a = f a := rfl

