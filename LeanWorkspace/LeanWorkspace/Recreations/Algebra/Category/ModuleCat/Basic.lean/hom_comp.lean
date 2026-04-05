import Mathlib

variable (R : Type u) [Ring R]

theorem hom_comp {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

