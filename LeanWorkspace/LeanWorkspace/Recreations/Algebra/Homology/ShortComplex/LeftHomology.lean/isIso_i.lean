import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.LeftHomologyData) {A : C}

theorem isIso_i (hg : S.g = 0) : IsIso h.i := ⟨h.liftK (𝟙 S.X₂) (by rw [hg, id_comp]),
    by simp only [← cancel_mono h.i, id_comp, assoc, CategoryTheory.ShortComplex.LeftHomologyData.liftK_i, comp_id], CategoryTheory.ShortComplex.LeftHomologyData.liftK_i _ _ _⟩

