import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

variable {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  (hkf : IsLimit kf) (hcc : IsColimit cc)
  {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
  (fac : kf.ι ≫ cc.π = π ≫ ι)
  [Epi π] [Mono ι]

theorem isoHomology_inv_homologyι :
    (CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology S hkf hcc fac).hom ≫ S.homologyι =
    ι ≫ (S.isoOpcyclesOfIsColimit hcc).hom := by
  rw [← cancel_mono (S.isoOpcyclesOfIsColimit hcc).inv, assoc, assoc, Iso.hom_inv_id,
    comp_id, ← CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology_hom_comp_ι S hkf hcc fac, Iso.hom_inv_id_assoc]

