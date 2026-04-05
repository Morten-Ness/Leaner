import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIsoAt_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] :
    QuasiIsoAt (φ ≫ φ') i ↔ QuasiIsoAt φ' i := by
  constructor
  · intro
    exact quasiIsoAt_of_comp_left φ φ' i
  · intro
    infer_instance

