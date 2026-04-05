import Mathlib

section

variable (R G : Type*) [CommRing R] [Group G] [TopologicalSpace R]

variable [TopologicalSpace G] [IsTopologicalGroup G]

set_option backward.isDefEq.respectTransparency false in
theorem d_comp_d (n : ℕ) :
    ContinuousCohomology.MultiInd.d R G n ≫ ContinuousCohomology.MultiInd.d R G (n + 1) = 0 := by
  induction n with
  | zero =>
    rw [ContinuousCohomology.MultiInd.d_succ, Preadditive.comp_sub, sub_eq_zero]
    rfl
  | succ n ih =>
    rw [ContinuousCohomology.MultiInd.d_succ R G (n + 1), Preadditive.comp_sub]
    nth_rw 2 [ContinuousCohomology.MultiInd.d_succ]
    rw [Preadditive.sub_comp, ← whiskerRight_comp, ih,
      Functor.whiskerRight_zero, sub_zero, sub_eq_zero]
    rfl

end
