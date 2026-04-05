import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

theorem biprod_total_f (i : ι) :
    (biprod.fst : K ⊞ L ⟶ K).f i ≫ (biprod.inl : K ⟶ K ⊞ L).f i +
      (biprod.snd : K ⊞ L ⟶ L).f i ≫ (biprod.inr : L ⟶ K ⊞ L).f i =
    𝟙 ((biprod K L).X i) := by
  simp [← comp_f, ← add_f_apply]

