import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

theorem kernel_ι_comp_cokernel_π_comp_cokernelToAbelianCoimage :
    (kernel.ι S.g ≫ cokernel.π S.f) ≫ S.cokernelToAbelianCoimage = 0 := by simp

