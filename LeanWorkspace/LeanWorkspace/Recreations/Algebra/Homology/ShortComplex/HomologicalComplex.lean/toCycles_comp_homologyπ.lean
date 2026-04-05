import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

theorem toCycles_comp_homologyπ [K.HasHomology j] :
    K.toCycles i j ≫ K.homologyπ j = 0 := K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

