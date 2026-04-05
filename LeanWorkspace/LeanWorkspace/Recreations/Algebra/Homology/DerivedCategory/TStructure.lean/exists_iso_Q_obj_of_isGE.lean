import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem exists_iso_Q_obj_of_isGE (X : DerivedCategory C) (n : ℤ) [hX : X.IsGE n] :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsStrictlyGE n), Nonempty (X ≅ Q.obj K) := by
  obtain ⟨K, e, _⟩ := hX
  exact ⟨K, inferInstance, ⟨e⟩⟩

