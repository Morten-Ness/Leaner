import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem mk' (h : S.LeftHomologyData) : CategoryTheory.ShortComplex.HasLeftHomology S := ⟨Nonempty.intro h⟩

