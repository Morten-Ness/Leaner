import Mathlib

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

variable (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem isIso_iff (f : S₁ ⟶ S₂) :
    IsIso f ↔ IsIso f.τ₁ ∧ IsIso f.τ₂ ∧ IsIso f.τ₃ := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨_, _, _⟩
  apply CategoryTheory.ShortComplex.isIso_of_isIso

