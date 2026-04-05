import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

variable {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  (hkf : IsLimit kf) (hcc : IsColimit cc)
  {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
  (fac : kf.ι ≫ cc.π = π ≫ ι)
  [Epi π] [Mono ι]

theorem isoHomology_hom_comp_ι :
    (CategoryTheory.ShortComplex.HomologyData.ofEpiMonoFactorisation.isoHomology S hkf hcc fac).inv ≫ ι = S.homologyι ≫ (S.isoOpcyclesOfIsColimit hcc).inv := by
  simp [← cancel_epi S.homologyπ, ← cancel_epi (S.isoCyclesOfIsLimit hkf).hom,
    ← π_comp_isoHomology_hom_assoc S hkf hcc fac, ← fac]

