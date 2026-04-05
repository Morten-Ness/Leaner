import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isLE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsLE n ↔ K.IsLE n := by
  have eq := fun i ↦ ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [DerivedCategory.isLE_iff, CochainComplex.isLE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

