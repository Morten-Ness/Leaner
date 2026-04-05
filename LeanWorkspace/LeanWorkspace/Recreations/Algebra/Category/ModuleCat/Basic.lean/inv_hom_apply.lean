import Mathlib

variable (R : Type u) [Ring R]

theorem inv_hom_apply {M N : ModuleCat.{v} R} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

