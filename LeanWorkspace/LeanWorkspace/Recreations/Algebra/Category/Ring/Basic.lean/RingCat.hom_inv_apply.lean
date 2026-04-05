import Mathlib

theorem hom_inv_apply {R S : RingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp

