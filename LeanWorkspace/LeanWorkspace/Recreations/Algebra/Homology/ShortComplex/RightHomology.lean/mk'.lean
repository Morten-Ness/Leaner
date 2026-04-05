import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem mk' (h : S.RightHomologyData) : CategoryTheory.ShortComplex.HasRightHomology S := ⟨Nonempty.intro h⟩

