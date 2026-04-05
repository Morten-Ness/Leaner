import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable [HasRightHomology S₁] [HasRightHomology S₂] (φ : S₁ ⟶ S₂)

theorem p_opcyclesMap : S₁.pOpcycles ≫ CategoryTheory.ShortComplex.opcyclesMap φ = φ.τ₂ ≫ S₂.pOpcycles := CategoryTheory.ShortComplex.p_opcyclesMap' _ _ _

