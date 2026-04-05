import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

theorem LeftHomologyData.lift_K_comp_cyclesIso_inv :
    h.liftK k hk ≫ h.cyclesIso.inv = S.liftCycles k hk := by
  rw [← h.liftCycles_comp_cyclesIso_hom, assoc, Iso.hom_inv_id, comp_id]

