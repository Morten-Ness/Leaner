import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

variable {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  (hkf : IsLimit kf) (hcc : IsColimit cc)
  {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
  (fac : kf.ι ≫ cc.π = π ≫ ι)
  [Epi π] [Mono ι]

theorem isoImage_ι :
    (CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoImage S hkf hcc fac).hom ≫ image.ι (S.iCycles ≫ S.pOpcycles) =
      ι ≫ (S.isoOpcyclesOfIsColimit hcc).hom := by
  apply image.isoStrongEpiMono_hom_comp_ι
  simp [← reassoc_of% fac]

