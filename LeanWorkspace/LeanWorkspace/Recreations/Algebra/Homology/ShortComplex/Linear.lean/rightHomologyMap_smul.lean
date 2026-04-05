import Mathlib

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]

variable {S₁ S₂ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

variable (a : R)

variable [S₁.HasRightHomology] [S₂.HasRightHomology]

theorem rightHomologyMap_smul : rightHomologyMap (a • φ) = a • rightHomologyMap φ := CategoryTheory.ShortComplex.rightHomologyMap'_smul _ _ _ _

