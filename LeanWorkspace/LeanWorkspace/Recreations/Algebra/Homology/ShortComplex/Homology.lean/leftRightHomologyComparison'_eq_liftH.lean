import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)

theorem leftRightHomologyComparison'_eq_liftH :
    CategoryTheory.ShortComplex.leftRightHomologyComparison' h₁ h₂ =
      h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
        (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
          RightHomologyData.p_g', LeftHomologyData.wi, comp_zero]) := rfl

