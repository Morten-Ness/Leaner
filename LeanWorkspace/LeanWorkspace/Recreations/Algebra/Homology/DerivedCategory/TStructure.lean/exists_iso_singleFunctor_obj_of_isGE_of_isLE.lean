import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    ∃ (Y : C), Nonempty (X ≅ (singleFunctor C n).obj Y) := by
  obtain ⟨K, _, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE X n n
  obtain ⟨Y, ⟨e'⟩⟩ := CochainComplex.exists_iso_single K n
  exact ⟨Y, ⟨e ≪≫ Q.mapIso e'⟩⟩

