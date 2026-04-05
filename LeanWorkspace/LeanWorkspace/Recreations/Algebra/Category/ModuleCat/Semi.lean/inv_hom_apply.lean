import Mathlib

variable (R : Type u) [Semiring R]

theorem inv_hom_apply {M N : SemimoduleCat.{v} R} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

