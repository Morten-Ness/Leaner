import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isGE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsGE n ↔ K.IsGE n := by
  have eq := fun i ↦ ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [DerivedCategory.isGE_iff, CochainComplex.isGE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

