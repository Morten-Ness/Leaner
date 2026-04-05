import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

theorem quotient_map_mem_quasiIso_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    HomotopyCategory.quasiIso C c ((quotient C c).map f) ↔ HomologicalComplex.quasiIso C c f := by
  have eq := fun (i : ι) => NatIso.isIso_map_iff (HomologicalComplexUpToQuasiIso.homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [HomologicalComplex.mem_quasiIso_iff, HomotopyCategory.mem_quasiIso_iff, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap, eq]

