import Mathlib

variable (R : Type u) [Semiring R]

theorem comp_apply {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
    (f ≫ g) x = g (f x) := by simp

