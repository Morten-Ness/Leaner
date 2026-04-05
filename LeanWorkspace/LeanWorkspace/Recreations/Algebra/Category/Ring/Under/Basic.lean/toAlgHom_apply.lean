import Mathlib

variable {R S : CommRingCat.{u}}

theorem toAlgHom_apply {A B : Under R} (f : A ⟶ B) (a : A) :
    CommRingCat.toAlgHom f a = f.right a := rfl

