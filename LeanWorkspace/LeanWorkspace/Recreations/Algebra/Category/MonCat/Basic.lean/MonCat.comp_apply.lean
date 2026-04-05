import Mathlib

theorem comp_apply {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

