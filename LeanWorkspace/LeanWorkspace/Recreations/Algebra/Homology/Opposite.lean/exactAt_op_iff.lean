import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem exactAt_op_iff (K : HomologicalComplex V c) {i : ι} :
    K.op.ExactAt i ↔ K.ExactAt i := ⟨fun h ↦ h.unop, fun h ↦ h.op⟩

