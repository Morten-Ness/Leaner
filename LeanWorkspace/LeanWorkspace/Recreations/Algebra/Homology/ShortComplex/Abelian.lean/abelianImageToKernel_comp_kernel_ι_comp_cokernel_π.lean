import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

theorem abelianImageToKernel_comp_kernel_ι_comp_cokernel_π :
    S.abelianImageToKernel ≫ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  simp

