import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [HasRightHomology S₁] [HasRightHomology S₂] (φ : S₁ ⟶ S₂)

theorem rightHomologyι_naturality :
    CategoryTheory.ShortComplex.rightHomologyMap φ ≫ S₂.rightHomologyι = S₁.rightHomologyι ≫ CategoryTheory.ShortComplex.opcyclesMap φ := CategoryTheory.ShortComplex.rightHomologyι_naturality' _ _ _

