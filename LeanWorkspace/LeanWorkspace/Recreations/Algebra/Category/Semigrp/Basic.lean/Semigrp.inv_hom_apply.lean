import Mathlib

theorem inv_hom_apply {X Y : Semigrp} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

