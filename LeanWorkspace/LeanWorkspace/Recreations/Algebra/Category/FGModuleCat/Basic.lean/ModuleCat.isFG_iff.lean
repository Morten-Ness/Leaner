import Mathlib

variable (R : Type u) [Ring R]

theorem ModuleCat.isFG_iff (V : ModuleCat.{v} R) :
    isFG R V ↔ Module.Finite R V := Iff.rfl

