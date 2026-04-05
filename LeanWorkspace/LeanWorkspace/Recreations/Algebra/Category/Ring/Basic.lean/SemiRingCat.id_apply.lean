import Mathlib

theorem id_apply (R : SemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

