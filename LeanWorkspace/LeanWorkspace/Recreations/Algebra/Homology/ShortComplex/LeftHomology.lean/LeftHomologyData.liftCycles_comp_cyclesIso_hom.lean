import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

theorem LeftHomologyData.liftCycles_comp_cyclesIso_hom :
    S.liftCycles k hk ≫ h.cyclesIso.hom = h.liftK k hk := by
  simp only [← cancel_mono h.i, assoc, LeftHomologyData.cyclesIso_hom_comp_i,
    CategoryTheory.ShortComplex.liftCycles_i, LeftHomologyData.liftK_i]

