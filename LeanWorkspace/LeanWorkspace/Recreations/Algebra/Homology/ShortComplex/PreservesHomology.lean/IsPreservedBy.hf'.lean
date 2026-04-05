import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S S₁ S₂ : ShortComplex C}

variable (h : S.LeftHomologyData) (F : C ⥤ D)

variable [F.PreservesZeroMorphisms]

variable [h.IsPreservedBy F]

theorem IsPreservedBy.hf' : PreservesColimit (parallelPair h.f' 0) F := IsPreservedBy.f'

