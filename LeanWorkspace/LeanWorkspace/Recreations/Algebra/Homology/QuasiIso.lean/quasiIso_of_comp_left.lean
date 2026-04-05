import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIso_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    [hφ : QuasiIso φ] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ' := by
  rw [← quasiIso_iff_comp_left φ φ']
  infer_instance

