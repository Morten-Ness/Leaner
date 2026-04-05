import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

omit [K.HasHomology i] in
theorem d_pOpcycles [K.HasHomology j] : K.d i j ≫ K.pOpcycles j = 0 := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.prev_eq' hij
    exact (K.sc j).f_pOpcycles
  · rw [K.shape _ _ hij, zero_comp]

