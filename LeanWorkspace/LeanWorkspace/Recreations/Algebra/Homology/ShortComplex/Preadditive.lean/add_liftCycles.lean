import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable (S : ShortComplex C) [S.HasLeftHomology] {A : C}
    (k k' : A ⟶ S.X₂) (hk : k ≫ S.g = 0) (hk' : k' ≫ S.g = 0)

theorem add_liftCycles :
    S.liftCycles k hk + S.liftCycles k' hk' =
      S.liftCycles (k + k') (by rw [add_comp, hk, hk', add_zero]) := by
  simp only [← cancel_mono S.iCycles, liftCycles_i, add_comp]

