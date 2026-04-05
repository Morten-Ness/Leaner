import Mathlib

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]

theorem ExactAt.op {K : HomologicalComplex V c} {i : ι} (h : K.ExactAt i) :
    K.op.ExactAt i := ShortComplex.Exact.op h

