import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isLE_iff (X : DerivedCategory C) (n : ℤ) :
    X.IsLE n ↔ ∀ (i : ℤ) (_ : n < i), IsZero ((homologyFunctor C i).obj X) := by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isLE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsLE n := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      apply (hX i hi).of_iso
      exact (homologyFunctorFactors C i).symm.app _ ≪≫
        (homologyFunctor C i).mapIso (Q.objObjPreimageIso X)
    exact ⟨(Q.objPreimage X).truncLE n, (Q.objObjPreimageIso X).symm ≪≫
      (asIso (Q.map ((Q.objPreimage X).ιTruncLE n))).symm, inferInstance⟩

