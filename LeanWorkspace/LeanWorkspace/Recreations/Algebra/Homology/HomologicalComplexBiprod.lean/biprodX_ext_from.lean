import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

variable {A : C} {i : ι}

theorem biprodX_ext_from {f g : (K ⊞ L).X i ⟶ A}
    (h₁ : (biprod.inl : K ⟶ K ⊞ L).f i ≫ f = (biprod.inl : K ⟶ K ⊞ L).f i ≫ g)
    (h₂ : (biprod.inr : L ⟶ K ⊞ L).f i ≫ f = (biprod.inr : L ⟶ K ⊞ L).f i ≫ g) :
    f = g := by
  simp [HomologicalComplex.biprodX_ext_from_iff, h₁, h₂]

