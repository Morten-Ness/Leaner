import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : RightHomologyData S) {A : C}
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

variable {cc : CokernelCofork S.f} (hcc : IsColimit cc)

theorem π_isoOpcyclesOfIsColimit_hom : cc.π ≫ (S.isoOpcyclesOfIsColimit hcc).hom = S.pOpcycles := IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one

