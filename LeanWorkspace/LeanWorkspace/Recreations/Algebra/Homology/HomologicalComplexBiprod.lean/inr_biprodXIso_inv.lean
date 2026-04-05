import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

theorem inr_biprodXIso_inv (i : ι) :
    biprod.inr ≫ (HomologicalComplex.biprodXIso K L i).inv = (biprod.inr : L ⟶ K ⊞ L).f i := by
  simp [HomologicalComplex.biprodXIso]

