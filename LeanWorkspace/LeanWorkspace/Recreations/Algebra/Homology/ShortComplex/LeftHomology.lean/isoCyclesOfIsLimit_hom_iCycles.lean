import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

variable {kf : KernelFork S.g} (hkf : IsLimit kf)

theorem isoCyclesOfIsLimit_hom_iCycles : (S.isoCyclesOfIsLimit hkf).hom ≫ S.iCycles = kf.ι := IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

