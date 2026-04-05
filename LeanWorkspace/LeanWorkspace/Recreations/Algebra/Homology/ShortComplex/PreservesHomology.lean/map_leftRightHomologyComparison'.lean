import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S S₁ S₂ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem map_leftRightHomologyComparison' (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hₗ : S.LeftHomologyData) (hᵣ : S.RightHomologyData) [hₗ.IsPreservedBy F] [hᵣ.IsPreservedBy F] :
    F.map (leftRightHomologyComparison' hₗ hᵣ) =
      leftRightHomologyComparison' (hₗ.map F) (hᵣ.map F) := by
  apply Cofork.IsColimit.hom_ext (hₗ.map F).hπ
  apply Fork.IsLimit.hom_ext (hᵣ.map F).hι
  trans F.map (hₗ.i ≫ hᵣ.p)
  · simp [← Functor.map_comp]
  trans (hₗ.map F).π ≫ CategoryTheory.ShortComplex.leftRightHomologyComparison'
    (hₗ.map F) (hᵣ.map F) ≫ (hᵣ.map F).ι
  · rw [CategoryTheory.ShortComplex.π_leftRightHomologyComparison'_ι]; simp
  · simp

