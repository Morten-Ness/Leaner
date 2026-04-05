import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [HasLeftHomology S₁] [HasLeftHomology S₂] (φ : S₁ ⟶ S₂)

theorem leftHomologyπ_naturality :
    S₁.leftHomologyπ ≫ CategoryTheory.ShortComplex.leftHomologyMap φ = CategoryTheory.ShortComplex.cyclesMap φ ≫ S₂.leftHomologyπ := CategoryTheory.ShortComplex.leftHomologyπ_naturality' _ _ _

