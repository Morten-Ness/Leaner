import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

theorem p_fromOpcycles :
    K.pOpcycles i ≫ K.fromOpcycles i j = K.d i j := HomologicalComplex.p_descOpcycles _ _ _ _ _

