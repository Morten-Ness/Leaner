import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem Acyclic.unop {K : HomologicalComplex Vᵒᵖ c} (h : K.Acyclic) :
    K.unop.Acyclic := fun i ↦ (h i).unop

