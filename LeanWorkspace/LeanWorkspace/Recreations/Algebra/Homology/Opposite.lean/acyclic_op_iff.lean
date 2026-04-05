import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem acyclic_op_iff (K : HomologicalComplex V c) :
    K.op.Acyclic ↔ K.Acyclic := ⟨fun h ↦ h.unop, fun h ↦ h.op⟩

