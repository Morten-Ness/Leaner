import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable [CategoryWithHomology C]

set_option backward.isDefEq.respectTransparency false in
theorem quasiIsoAt_shift_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n i j : ℤ) (h : n + i = j) :
    QuasiIsoAt (φ⟦n⟧') i ↔ QuasiIsoAt φ j := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (NatIso.isIso_map_iff
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n i j h) φ)

