import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]

theorem isIso_pOpcycles : IsIso (K.pOpcycles j) := by
  obtain rfl := hi
  exact ShortComplex.isIso_pOpcycles _ h

