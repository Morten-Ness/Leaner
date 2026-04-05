import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}

variable [S₁.HasHomology] [S₂.HasHomology]

theorem homologyMap_neg : homologyMap (-φ) = -homologyMap φ := CategoryTheory.ShortComplex.homologyMap'_neg _ _

