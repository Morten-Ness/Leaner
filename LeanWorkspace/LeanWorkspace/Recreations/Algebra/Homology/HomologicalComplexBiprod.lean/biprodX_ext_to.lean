import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

variable {A : C} {i : ι}

theorem biprodX_ext_to {f g : A ⟶ (K ⊞ L).X i}
    (h₁ : f ≫ (biprod.fst : K ⊞ L ⟶ K).f i = g ≫ (biprod.fst : K ⊞ L ⟶ K).f i)
    (h₂ : f ≫ (biprod.snd : K ⊞ L ⟶ L).f i = g ≫ (biprod.snd : K ⊞ L ⟶ L).f i) :
    f = g := by
  simp [HomologicalComplex.biprodX_ext_to_iff, h₁, h₂]

