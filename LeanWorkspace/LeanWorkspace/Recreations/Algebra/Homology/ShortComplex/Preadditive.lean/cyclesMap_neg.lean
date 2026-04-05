import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

theorem cyclesMap_neg : cyclesMap (-φ) = -cyclesMap φ := CategoryTheory.ShortComplex.cyclesMap'_neg _ _

