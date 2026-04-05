import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

include iso in
theorem hasHomology_of_iso [K.HasHomology i] : L.HasHomology i := ShortComplex.hasHomology_of_iso
    ((HomologicalComplex.shortComplexFunctor _ _ i).mapIso iso : K.sc i ≅ L.sc i)

