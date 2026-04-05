import Mathlib

variable (R : Type u) [Ring R]

theorem hom_inv_apply {M N : ModuleCat.{v} R} (e : M ≅ N) (x : N) : e.hom (e.inv x) = x := by
  simp

