import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIso_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_right φ φ']

