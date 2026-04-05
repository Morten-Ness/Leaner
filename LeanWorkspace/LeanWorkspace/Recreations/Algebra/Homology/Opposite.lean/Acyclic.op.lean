import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem Acyclic.op {K : HomologicalComplex V c} (h : K.Acyclic) :
    K.op.Acyclic := fun i ↦ (h i).op

