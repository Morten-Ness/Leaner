import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : RightHomologyData S) {A : C}
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

theorem rightHomologyι_comp_fromOpcycles :
    S.rightHomologyι ≫ S.fromOpcycles = 0 := S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary S.g (𝟙 _) (by rw [comp_id])

