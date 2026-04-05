import Mathlib

theorem comp_apply {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

