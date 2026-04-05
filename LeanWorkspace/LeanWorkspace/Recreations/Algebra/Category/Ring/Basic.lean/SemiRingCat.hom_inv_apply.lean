import Mathlib

theorem hom_inv_apply {R S : SemiRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

