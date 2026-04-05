import Mathlib

theorem id_apply (R : CommSemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

