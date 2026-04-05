import Mathlib

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem image.fac : ModuleCat.factorThruImage f ≫ ModuleCat.image.ι f = f := rfl

attribute [local simp] ModuleCat.image.fac

