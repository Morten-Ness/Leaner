import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

theorem toCycles_eq_zero [K.HasHomology j] (hij : ¬ c.Rel i j) :
    K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), HomologicalComplex.toCycles_i, zero_comp, K.shape _ _ hij]

