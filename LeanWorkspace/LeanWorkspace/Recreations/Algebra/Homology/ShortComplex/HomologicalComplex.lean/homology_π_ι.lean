import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

variable [L.HasHomology i] [M.HasHomology i]

theorem homology_π_ι :
    K.homologyπ i ≫ K.homologyι i = K.iCycles i ≫ K.pOpcycles i := (K.sc i).homology_π_ι

