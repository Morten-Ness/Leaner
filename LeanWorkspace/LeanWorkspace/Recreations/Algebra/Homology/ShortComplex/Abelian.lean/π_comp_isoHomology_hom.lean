import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

variable {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  (hkf : IsLimit kf) (hcc : IsColimit cc)
  {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
  (fac : kf.ι ≫ cc.π = π ≫ ι)
  [Epi π] [Mono ι]

theorem π_comp_isoHomology_hom :
    π ≫ (CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology S hkf hcc fac).hom = (S.isoCyclesOfIsLimit hkf).hom ≫ S.homologyπ := by
  dsimp [CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology]
  simp [← cancel_mono (S.homologyIsoImageICyclesCompPOpcycles.hom),
    ← cancel_mono (image.ι (S.iCycles ≫ S.pOpcycles)),
    ← reassoc_of% fac]

