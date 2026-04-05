import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

variable [S₁.HasRightHomology] [S₂.HasRightHomology]

theorem opcyclesMap_add : opcyclesMap (φ + φ') = opcyclesMap φ + opcyclesMap φ' := CategoryTheory.ShortComplex.opcyclesMap'_add _ _

