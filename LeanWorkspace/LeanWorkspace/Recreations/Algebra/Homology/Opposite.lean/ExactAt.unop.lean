import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem ExactAt.unop {K : HomologicalComplex Vᵒᵖ c} {i : ι} (h : K.ExactAt i) :
    K.unop.ExactAt i := ShortComplex.Exact.unop h

