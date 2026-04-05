import Mathlib

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]

variable {S₁ S₂ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}

variable (a : R)

theorem homologyMap_smul [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (a • φ) = a • homologyMap φ := CategoryTheory.ShortComplex.homologyMap'_smul _ _ _

