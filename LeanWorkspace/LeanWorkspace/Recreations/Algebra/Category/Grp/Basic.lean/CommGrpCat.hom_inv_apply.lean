import Mathlib

theorem hom_inv_apply {X Y : CommGrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

