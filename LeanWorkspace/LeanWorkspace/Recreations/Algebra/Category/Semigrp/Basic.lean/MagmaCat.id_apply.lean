import Mathlib

theorem id_apply (M : MagmaCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

