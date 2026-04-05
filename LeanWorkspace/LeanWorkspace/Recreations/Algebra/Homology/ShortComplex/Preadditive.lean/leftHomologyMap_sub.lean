import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

theorem leftHomologyMap_sub : leftHomologyMap (φ - φ') = leftHomologyMap φ - leftHomologyMap φ' := CategoryTheory.ShortComplex.leftHomologyMap'_sub _ _

