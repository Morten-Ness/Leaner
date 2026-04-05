import Mathlib

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι)
  [K.HasHomology i] [K.HasHomology j] [L.HasHomology i] [L.HasHomology j]

theorem opcyclesToCycles_iCycles : K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOpcycles i j := by
  dsimp only [HomologicalComplex.opcyclesToCycles]
  simp

