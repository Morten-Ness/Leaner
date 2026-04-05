import Mathlib

variable (R : Type u) [Semiring R]

theorem hom_inv_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : N) : e.hom (e.inv x) = x := by
  simp

