import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

theorem liftCycles_leftHomologyπ_eq_zero_of_boundary (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    S.liftCycles k (by rw [hx, assoc, S.zero, comp_zero]) ≫ S.leftHomologyπ = 0 := LeftHomologyData.liftK_π_eq_zero_of_boundary _ k x hx

