import Mathlib

theorem inv_hom_apply {M N : MagmaCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

