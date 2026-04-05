import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : RightHomologyData S) {A : C}
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

theorem rightHomologyι_descOpcycles_π_eq_zero_of_boundary (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
    S.rightHomologyι ≫ S.descOpcycles k (by rw [hx, S.zero_assoc, zero_comp]) = 0 := RightHomologyData.ι_descQ_eq_zero_of_boundary _ k x hx

