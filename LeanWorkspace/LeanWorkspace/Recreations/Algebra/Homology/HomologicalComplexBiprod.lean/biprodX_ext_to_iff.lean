import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

variable {A : C} {i : ι}

theorem biprodX_ext_to_iff {f g : A ⟶ (K ⊞ L).X i} :
    f = g ↔ f ≫ (biprod.fst : K ⊞ L ⟶ K).f i = g ≫ (biprod.fst : K ⊞ L ⟶ K).f i ∧
      f ≫ (biprod.snd : K ⊞ L ⟶ L).f i = g ≫ (biprod.snd : K ⊞ L ⟶ L).f i := by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rw [← cancel_mono (𝟙 _)]
  simp [← HomologicalComplex.biprod_total_f, reassoc_of% h₁, reassoc_of% h₂]

