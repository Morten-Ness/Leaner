import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

variable {kf : KernelFork S.g} {cc : CokernelCofork S.f}
  (hkf : IsLimit kf) (hcc : IsColimit cc)
  {H : C} {π : kf.pt ⟶ H} {ι : H ⟶ cc.pt}
  (fac : kf.ι ≫ cc.π = π ≫ ι)
  [Epi π] [Mono ι]

set_option backward.isDefEq.respectTransparency false in
theorem f'_eq :
    hkf.lift (KernelFork.ofι S.f S.zero) =
      S.toCycles ≫ (S.isoCyclesOfIsLimit hkf).inv := by
  have := Fork.IsLimit.mono hkf
  simp [← cancel_mono kf.ι]

