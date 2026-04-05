import Mathlib

theorem hom_inv_apply {M N : CommMonCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

