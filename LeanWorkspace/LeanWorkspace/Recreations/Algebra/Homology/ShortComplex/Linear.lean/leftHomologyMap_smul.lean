import Mathlib

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]

variable {S₁ S₂ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

variable (a : R)

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

theorem leftHomologyMap_smul : leftHomologyMap (a • φ) = a • leftHomologyMap φ := CategoryTheory.ShortComplex.leftHomologyMap'_smul _ _ _ _

