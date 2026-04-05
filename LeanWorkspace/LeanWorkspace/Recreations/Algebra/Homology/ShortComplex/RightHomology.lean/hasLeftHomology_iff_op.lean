import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem hasLeftHomology_iff_op (S : CategoryTheory.ShortComplex C) :
    S.HasLeftHomology ↔ S.op.HasRightHomology := ⟨fun _ => inferInstance, fun _ => HasLeftHomology.mk' S.op.rightHomologyData.unop⟩

