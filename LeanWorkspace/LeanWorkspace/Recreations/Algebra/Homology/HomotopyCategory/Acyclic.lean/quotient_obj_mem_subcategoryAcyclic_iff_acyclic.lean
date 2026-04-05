import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

theorem quotient_obj_mem_subcategoryAcyclic_iff_acyclic (K : CochainComplex C ℤ) :
    HomotopyCategory.subcategoryAcyclic C ((quotient _ _).obj K) ↔ K.Acyclic := HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt _

