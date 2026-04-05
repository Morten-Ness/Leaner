import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

theorem shiftFunctor₁XXIso_refl (a b x : ℤ) :
    K.shiftFunctor₁XXIso a x (a + x) rfl b = Iso.refl _ := rfl

