import Mathlib

variable {R S : CommRingCat.{u}}

theorem toAlgHom_comp {A B C : Under R} (f : A ⟶ B) (g : B ⟶ C) :
    CommRingCat.toAlgHom (f ≫ g) = (CommRingCat.toAlgHom g).comp (CommRingCat.toAlgHom f) := rfl

