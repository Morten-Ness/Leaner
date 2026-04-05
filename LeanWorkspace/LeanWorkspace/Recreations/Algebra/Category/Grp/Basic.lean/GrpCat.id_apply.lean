import Mathlib

theorem id_apply (X : GrpCat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

