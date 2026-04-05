import Mathlib

theorem inv_hom_apply {X Y : GrpCat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

-- This is essentially an alias for `Iso.inv_hom_id_apply`; consider deprecation?

