import Mathlib

variable (R : Type u) [Ring R]

theorem comp_apply {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    (f ≫ g) x = g (f x) := by simp

