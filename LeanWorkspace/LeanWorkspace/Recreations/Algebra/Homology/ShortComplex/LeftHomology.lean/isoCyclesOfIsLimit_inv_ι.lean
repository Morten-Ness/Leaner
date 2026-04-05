import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

variable {kf : KernelFork S.g} (hkf : IsLimit kf)

theorem isoCyclesOfIsLimit_inv_ι : (S.isoCyclesOfIsLimit hkf).inv ≫ kf.ι = S.iCycles := IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

