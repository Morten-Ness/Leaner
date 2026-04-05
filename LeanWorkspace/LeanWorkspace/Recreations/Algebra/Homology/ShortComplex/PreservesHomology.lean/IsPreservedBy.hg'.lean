import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S S₁ S₂ : ShortComplex C}

variable (h : S.RightHomologyData) (F : C ⥤ D)

variable [F.PreservesZeroMorphisms]

variable [h.IsPreservedBy F]

theorem IsPreservedBy.hg' : PreservesLimit (parallelPair h.g' 0) F := @IsPreservedBy.g' _ _ _ _ _ _ _ h F _ _

