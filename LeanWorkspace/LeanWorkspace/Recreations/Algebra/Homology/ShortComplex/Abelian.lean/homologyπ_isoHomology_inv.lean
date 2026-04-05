import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

variable {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  (hkf : IsLimit kf) (hcc : IsColimit cc)
  {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
  (fac : kf.ι ≫ cc.π = π ≫ ι)
  [Epi π] [Mono ι]

theorem homologyπ_isoHomology_inv :
    S.homologyπ ≫ (CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology S hkf hcc fac).inv = (S.isoCyclesOfIsLimit hkf).inv ≫ π := by
  simp only [← cancel_mono (CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology S hkf hcc fac).hom, assoc, Iso.inv_hom_id, comp_id,
    CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.π_comp_isoHomology_hom, Iso.inv_hom_id_assoc]

