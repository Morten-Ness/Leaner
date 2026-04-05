import Mathlib

theorem id_apply (R : CommRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

