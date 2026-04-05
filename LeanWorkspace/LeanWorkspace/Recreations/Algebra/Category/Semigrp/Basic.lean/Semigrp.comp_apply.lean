import Mathlib

theorem comp_apply {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

