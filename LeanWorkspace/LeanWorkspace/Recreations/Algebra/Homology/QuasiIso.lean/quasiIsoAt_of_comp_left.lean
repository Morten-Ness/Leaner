import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIsoAt_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] [hφφ' : QuasiIsoAt (φ ≫ φ') i] :
    QuasiIsoAt φ' i := by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ i) (homologyMap φ' i)

