import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

theorem quasiIso_eq_subcategoryAcyclic_W :
    quasiIso C (ComplexShape.up ℤ) = (HomotopyCategory.subcategoryAcyclic C).trW := by
  ext K L f
  exact ((homologyFunctor C (ComplexShape.up ℤ) 0).mem_homologicalKernel_trW_iff f).symm

