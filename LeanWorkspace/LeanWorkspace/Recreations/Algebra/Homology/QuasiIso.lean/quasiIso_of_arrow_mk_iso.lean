import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIso_of_arrow_mk_iso (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ')
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [∀ i, K'.HasHomology i] [∀ i, L'.HasHomology i]
    [hφ : QuasiIso φ] : QuasiIso φ' := by
  simpa only [← quasiIso_iff_of_arrow_mk_iso φ φ' e]

