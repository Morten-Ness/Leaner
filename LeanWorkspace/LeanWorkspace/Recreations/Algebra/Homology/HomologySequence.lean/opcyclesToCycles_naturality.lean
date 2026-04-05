import Mathlib

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι)
  [K.HasHomology i] [K.HasHomology j] [L.HasHomology i] [L.HasHomology j]

theorem opcyclesToCycles_naturality :
    opcyclesMap φ i ≫ HomologicalComplex.opcyclesToCycles L i j = HomologicalComplex.opcyclesToCycles K i j ≫ cyclesMap φ j := by
  simp only [← cancel_mono (L.iCycles j), ← cancel_epi (K.pOpcycles i),
    assoc, p_opcyclesMap_assoc, HomologicalComplex.pOpcycles_opcyclesToCycles_iCycles, Hom.comm, cyclesMap_i,
    pOpcycles_opcyclesToCycles_iCycles_assoc]

