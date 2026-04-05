import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem hasRightHomology_iff_op (S : CategoryTheory.ShortComplex C) :
    S.HasRightHomology ↔ S.op.HasLeftHomology := ⟨fun _ => inferInstance, fun _ => HasRightHomology.mk' S.op.leftHomologyData.unop⟩

