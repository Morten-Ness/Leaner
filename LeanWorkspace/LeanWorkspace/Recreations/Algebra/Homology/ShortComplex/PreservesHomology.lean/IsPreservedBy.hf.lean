import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S S₁ S₂ : ShortComplex C}

variable (h : S.RightHomologyData) (F : C ⥤ D)

variable [F.PreservesZeroMorphisms]

variable [h.IsPreservedBy F]

include h in
theorem IsPreservedBy.hf : PreservesColimit (parallelPair S.f 0) F := @IsPreservedBy.f _ _ _ _ _ _ _ h F _ _

