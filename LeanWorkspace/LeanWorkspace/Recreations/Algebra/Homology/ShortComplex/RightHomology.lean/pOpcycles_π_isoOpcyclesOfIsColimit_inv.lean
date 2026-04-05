import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : RightHomologyData S) {A : C}
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

variable {cc : CokernelCofork S.f} (hcc : IsColimit cc)

theorem pOpcycles_π_isoOpcyclesOfIsColimit_inv :
    S.pOpcycles ≫ (S.isoOpcyclesOfIsColimit hcc).inv = cc.π := IsColimit.comp_coconePointUniqueUpToIso_inv _ S.opcyclesIsCokernel WalkingParallelPair.one

