import Mathlib

variable (R : Type u) [Ring R]

theorem forget_map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (forget (ModuleCat.{v} R)).map f = (f : _ → _) := rfl

