import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

variable {M : HomologicalComplex C c}

theorem biprod_inr_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.desc α β).f i = β.f i := by
  rw [← comp_f, biprod.inr_desc]

