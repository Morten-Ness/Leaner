import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

theorem abelianImageToKernel_comp_kernel_ι :
    S.abelianImageToKernel ≫ kernel.ι S.g = Abelian.image.ι S.f := kernel.lift_ι _ _ _

