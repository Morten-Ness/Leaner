import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

variable {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  (hkf : IsLimit kf) (hcc : IsColimit cc)
  {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
  (fac : kf.ι ≫ cc.π = π ≫ ι)
  [Epi π] [Mono ι]

set_option backward.isDefEq.respectTransparency false in
theorem g'_eq : hcc.desc (CokernelCofork.ofπ S.g S.zero) =
    (S.isoOpcyclesOfIsColimit hcc).hom ≫ S.fromOpcycles := by
  have := Cofork.IsColimit.epi hcc
  simp [← cancel_epi cc.π]

