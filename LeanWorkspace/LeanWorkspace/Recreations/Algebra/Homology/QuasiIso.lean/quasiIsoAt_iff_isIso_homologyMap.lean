import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIsoAt_iff_isIso_homologyMap (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔ IsIso (homologyMap f i) := by
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  rfl

