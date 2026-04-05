import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [HasRightHomology S₁] [HasRightHomology S₂] (φ : S₁ ⟶ S₂)

theorem fromOpcycles_naturality : CategoryTheory.ShortComplex.opcyclesMap φ ≫ S₂.fromOpcycles = S₁.fromOpcycles ≫ φ.τ₃ := CategoryTheory.ShortComplex.opcyclesMap'_g' _ _ _

