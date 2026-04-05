import Mathlib

variable (R : Type u) [Ring R]

theorem forget_obj {M : ModuleCat.{v} R} : (forget (ModuleCat.{v} R)).obj M = M := rfl

