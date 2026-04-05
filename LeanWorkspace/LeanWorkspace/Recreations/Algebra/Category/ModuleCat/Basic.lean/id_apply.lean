import Mathlib

variable (R : Type u) [Ring R]

theorem id_apply (M : ModuleCat.{v} R) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

