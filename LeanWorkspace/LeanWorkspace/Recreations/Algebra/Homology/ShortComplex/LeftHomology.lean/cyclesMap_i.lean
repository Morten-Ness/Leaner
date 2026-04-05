import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable [HasLeftHomology S₁] [HasLeftHomology S₂] (φ : S₁ ⟶ S₂)

theorem cyclesMap_i : CategoryTheory.ShortComplex.cyclesMap φ ≫ S₂.iCycles = S₁.iCycles ≫ φ.τ₂ := CategoryTheory.ShortComplex.cyclesMap'_i _ _ _

