import Mathlib

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem exists_iso_Q_obj_of_isGE (X : DerivedCategory C) (n : ℤ) [hX : X.IsGE n] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE n), Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem exists_iso_Q_obj_of_isGE_of_isLE (X : DerivedCategory C) (a b : ℤ) [X.IsGE a] [X.IsLE b] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE a) (_ : K.IsStrictlyLE b),
      Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE b
  have : K.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso e a
  exact ⟨K.truncGE a, inferInstance, inferInstance, ⟨e ≪≫ asIso (Q.map (K.πTruncGE a))⟩⟩

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem exists_iso_Q_obj_of_isLE (X : DerivedCategory C) (n : ℤ) [hX : X.IsLE n] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyLE n), Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    ∃ (Y : C), Nonempty (X ≅ (singleFunctor C n).obj Y) := by
  obtain ⟨K, _, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE X n n
  obtain ⟨Y, ⟨e'⟩⟩ := CochainComplex.exists_iso_single K n
  exact ⟨Y, ⟨e ≪≫ Q.mapIso e'⟩⟩

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isGE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsGE n ↔ K.IsGE n := by
  have eq := fun i ↦ ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [DerivedCategory.isGE_iff, CochainComplex.isGE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isGE_iff (X : DerivedCategory C) (n : ℤ) :
    X.IsGE n ↔ ∀ (i : ℤ) (_ : i < n), IsZero ((homologyFunctor C i).obj X) := by
  constructor
  · rintro ⟨K, e, _⟩ i hi
    apply ((K.exactAt_of_isGE n i hi).isZero_homology).of_iso
    exact (homologyFunctor C i).mapIso e ≪≫ (homologyFunctorFactors C i).app K
  · intro hX
    have : (Q.objPreimage X).IsGE n := by
      rw [CochainComplex.isGE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      apply (hX i hi).of_iso
      exact (homologyFunctorFactors C i).symm.app _ ≪≫
        (homologyFunctor C i).mapIso (Q.objObjPreimageIso X)
    exact ⟨(Q.objPreimage X).truncGE n, (Q.objObjPreimageIso X).symm ≪≫
      asIso (Q.map ((Q.objPreimage X).πTruncGE n)), inferInstance⟩

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isLE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsLE n ↔ K.IsLE n := by
  have eq := fun i ↦ ((homologyFunctorFactors C i).app K).isZero_iff
  simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at eq
  simp only [DerivedCategory.isLE_iff, CochainComplex.isLE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology, eq]

end

section

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

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isZero_of_isGE (X : DerivedCategory C) (n i : ℤ) (hi : i < n) [hX : X.IsGE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [DerivedCategory.isGE_iff] at hX
  exact hX i hi

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isZero_of_isLE (X : DerivedCategory C) (n i : ℤ) (hi : n < i) [hX : X.IsLE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [DerivedCategory.isLE_iff] at hX
  exact hX i hi

end
