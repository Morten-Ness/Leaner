import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

theorem homologyι_comp_fromOpcycles :
    K.homologyι i ≫ K.fromOpcycles i j = 0 := K.homologyι_descOpcycles_eq_zero_of_boundary (K.d i j) _ rfl (𝟙 _) (by simp)

