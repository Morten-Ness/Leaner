import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

theorem inl_biprodXIso_inv (i : ι) :
    biprod.inl ≫ (HomologicalComplex.biprodXIso K L i).inv = (biprod.inl : K ⟶ K ⊞ L).f i := by
  simp [HomologicalComplex.biprodXIso]

