import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.RightHomologyData) {A : C}

theorem isIso_p (hf : S.f = 0) : IsIso h.p := ⟨h.descQ (𝟙 S.X₂) (by rw [hf, comp_id]), CategoryTheory.ShortComplex.RightHomologyData.p_descQ _ _ _, by
    simp only [← cancel_epi h.p, p_descQ_assoc, id_comp, comp_id]⟩

