import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

variable [L.HasHomology i] [M.HasHomology i]

theorem cyclesMap_i : HomologicalComplex.cyclesMap φ i ≫ L.iCycles i = K.iCycles i ≫ φ.f i := ShortComplex.cyclesMap_i _

