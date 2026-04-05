import Mathlib

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι)
  [K.HasHomology i] [K.HasHomology j] [L.HasHomology i] [L.HasHomology j]

theorem pOpcycles_opcyclesToCycles :
    K.pOpcycles i ≫ K.opcyclesToCycles i j = K.toCycles i j := by
  simp only [← cancel_mono (K.iCycles j), assoc, HomologicalComplex.opcyclesToCycles_iCycles,
    p_fromOpcycles, toCycles_i]

