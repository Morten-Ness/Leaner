import Mathlib

theorem hom_inv_apply {X Y : GrpCat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

