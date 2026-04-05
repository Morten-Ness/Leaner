import Mathlib

theorem inv_hom_apply {R S : SemiRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp

