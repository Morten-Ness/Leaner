import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

theorem cokernel_π_comp_cokernelToAbelianCoimage :
    cokernel.π S.f ≫ S.cokernelToAbelianCoimage = Abelian.coimage.π S.g := cokernel.π_desc _ _ _

