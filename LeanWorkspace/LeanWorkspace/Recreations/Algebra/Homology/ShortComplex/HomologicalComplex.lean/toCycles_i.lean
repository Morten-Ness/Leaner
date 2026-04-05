import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

theorem toCycles_i [K.HasHomology j] :
    K.toCycles i j ≫ K.iCycles j = K.d i j := HomologicalComplex.liftCycles_i _ _ _ _ _

