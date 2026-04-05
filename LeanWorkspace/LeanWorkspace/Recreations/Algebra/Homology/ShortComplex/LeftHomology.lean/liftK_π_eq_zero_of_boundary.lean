import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.LeftHomologyData) {A : C}

theorem liftK_π_eq_zero_of_boundary (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    h.liftK k (by rw [hx, assoc, S.zero, comp_zero]) ≫ h.π = 0 := by
  rw [show 0 = (x ≫ h.f') ≫ h.π by simp]
  congr 1
  simp only [← cancel_mono h.i, hx, CategoryTheory.ShortComplex.LeftHomologyData.liftK_i, assoc, f'_i]

