import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

theorem biprodXIso_hom_snd (i : ι) :
    (HomologicalComplex.biprodXIso K L i).hom ≫ biprod.snd = (biprod.snd : K ⊞ L ⟶ L).f i := by
  simp [HomologicalComplex.biprodXIso]

