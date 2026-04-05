import Mathlib

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι)
  [K.HasHomology i] [K.HasHomology j] [L.HasHomology i] [L.HasHomology j]

theorem homologyι_opcyclesToCycles :
    K.homologyι i ≫ K.opcyclesToCycles i j = 0 := by
  simp only [← cancel_mono (K.iCycles j), assoc, HomologicalComplex.opcyclesToCycles_iCycles,
    homologyι_comp_fromOpcycles, zero_comp]

