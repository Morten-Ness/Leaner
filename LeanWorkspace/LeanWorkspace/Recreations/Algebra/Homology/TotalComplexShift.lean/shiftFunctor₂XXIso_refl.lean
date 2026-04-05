import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

theorem shiftFunctor₂XXIso_refl (a b y : ℤ) :
    K.shiftFunctor₂XXIso a b y (b + y) rfl = Iso.refl _ := rfl

