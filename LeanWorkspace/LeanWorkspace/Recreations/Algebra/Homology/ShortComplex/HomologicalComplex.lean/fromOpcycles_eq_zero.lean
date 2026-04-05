import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

theorem fromOpcycles_eq_zero (hij : ¬ c.Rel i j) :
    K.fromOpcycles i j = 0 := by
  rw [← cancel_epi (K.pOpcycles i), HomologicalComplex.p_fromOpcycles, comp_zero, K.shape _ _ hij]

