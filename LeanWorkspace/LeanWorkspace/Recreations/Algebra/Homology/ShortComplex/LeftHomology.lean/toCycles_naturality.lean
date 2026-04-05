import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [HasLeftHomology S₁] [HasLeftHomology S₂] (φ : S₁ ⟶ S₂)

theorem toCycles_naturality : S₁.toCycles ≫ CategoryTheory.ShortComplex.cyclesMap φ = φ.τ₁ ≫ S₂.toCycles := CategoryTheory.ShortComplex.f'_cyclesMap' _ _ _

