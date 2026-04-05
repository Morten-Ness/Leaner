import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable (F : C ⥤ D)

variable [PreservesZeroMorphisms F]

theorem PreservesHomology.preservesCokernel [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) F := PreservesHomology.preservesCokernels _

noncomputable instance preservesHomologyOfExact
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] : F.PreservesHomology where

