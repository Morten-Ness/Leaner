import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

variable [L.HasHomology i] [M.HasHomology i]

theorem homologyι_naturality :
    HomologicalComplex.homologyMap φ i ≫ L.homologyι i = K.homologyι i ≫ HomologicalComplex.opcyclesMap φ i := ShortComplex.homologyι_naturality _

