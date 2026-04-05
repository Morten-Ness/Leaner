import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

theorem HomologyData.map_homologyMap'
    [h₁.left.IsPreservedBy F] [h₁.right.IsPreservedBy F]
    [h₂.left.IsPreservedBy F] [h₂.right.IsPreservedBy F] :
    F.map (CategoryTheory.ShortComplex.homologyMap' φ h₁ h₂) =
      CategoryTheory.ShortComplex.homologyMap' (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) := LeftHomologyData.map_leftHomologyMap' _ _ _ _

