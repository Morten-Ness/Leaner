import Mathlib

variable {R S : CommRingCat.{u}}

theorem toUnder_inv_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (b : B) :
    f.toUnder.inv.right b = f.symm b := rfl

