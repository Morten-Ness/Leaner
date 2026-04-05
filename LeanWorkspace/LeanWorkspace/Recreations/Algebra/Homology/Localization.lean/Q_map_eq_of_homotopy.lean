import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

variable [(HomologicalComplex.quasiIso C c).HasLocalization] [c.QFactorsThroughHomotopy C]

theorem Q_map_eq_of_homotopy {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    Q.map f = Q.map g := (ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization h).map_eq Q

