import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

theorem quotient_obj_mem_subcategoryAcyclic_iff_exactAt (K : CochainComplex C ℤ) :
    HomotopyCategory.subcategoryAcyclic C ((quotient _ _).obj K) ↔ ∀ (n : ℤ), K.ExactAt n := by
  rw [HomotopyCategory.mem_subcategoryAcyclic_iff]
  refine forall_congr' (fun n => ?_)
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app K).isZero_iff

