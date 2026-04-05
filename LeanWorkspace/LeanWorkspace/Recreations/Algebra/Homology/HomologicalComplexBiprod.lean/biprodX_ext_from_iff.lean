import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

variable {A : C} {i : ι}

theorem biprodX_ext_from_iff {f g : (K ⊞ L).X i ⟶ A} :
    f = g ↔ (biprod.inl : K ⟶ K ⊞ L).f i ≫ f = (biprod.inl : K ⟶ K ⊞ L).f i ≫ g ∧
      (biprod.inr : L ⟶ K ⊞ L).f i ≫ f = (biprod.inr : L ⟶ K ⊞ L).f i ≫ g := by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rw [← cancel_epi (𝟙 _)]
  simp [← HomologicalComplex.biprod_total_f, h₁, h₂]

