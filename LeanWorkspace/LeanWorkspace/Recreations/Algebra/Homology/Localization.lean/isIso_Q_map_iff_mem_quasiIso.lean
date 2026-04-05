import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [HasZeroMorphisms C]
  [CategoryWithHomology C]

variable [(HomologicalComplex.quasiIso C c).HasLocalization]

theorem isIso_Q_map_iff_mem_quasiIso {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsIso (Q.map f) ↔ HomologicalComplex.quasiIso C c f := by
  constructor
  · intro h
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine (NatIso.isIso_map_iff (HomologicalComplexUpToQuasiIso.homologyFunctorFactors C c i) f).1 ?_
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.quasiIso C c) _ h

