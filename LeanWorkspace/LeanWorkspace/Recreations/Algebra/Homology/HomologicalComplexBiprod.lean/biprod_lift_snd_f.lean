import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

variable {M : HomologicalComplex C c}

theorem biprod_lift_snd_f (α : M ⟶ K) (β : M ⟶ L) (i : ι) :
    (biprod.lift α β).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = β.f i := by
  rw [← comp_f, biprod.lift_snd]

