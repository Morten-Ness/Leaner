import Mathlib

variable {ι : Type*} (c : ComplexShape ι) (hc : ∀ j, ∃ i, c.Rel i j)
  (C : Type*) [Category* C] [Preadditive C] [HasBinaryBiproducts C]

theorem ComplexShape.quotient_isLocalization :
    (HomotopyCategory.quotient C c).IsLocalization
      (HomologicalComplex.homotopyEquivalences _ _) := by
  apply Functor.IsLocalization.mk'
  all_goals apply c.strictUniversalPropertyFixedTargetQuotient hc

