import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

variable [L.HasHomology i] [M.HasHomology i]

theorem homologyπ_naturality :
    K.homologyπ i ≫ HomologicalComplex.homologyMap φ i = HomologicalComplex.cyclesMap φ i ≫ L.homologyπ i := ShortComplex.homologyπ_naturality _

