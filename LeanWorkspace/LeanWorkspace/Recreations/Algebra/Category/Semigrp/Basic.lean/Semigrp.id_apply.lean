import Mathlib

theorem id_apply (X : Semigrp) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

