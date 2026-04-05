import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable (h : S.LeftHomologyData) {A : C}

theorem isIso_π (hf : S.f = 0) : IsIso h.π := by
  have ⟨φ, hφ⟩ := CokernelCofork.IsColimit.desc' h.hπ' (𝟙 _)
    (by rw [← cancel_mono h.i, comp_id, f'_i, zero_comp, hf])
  dsimp at hφ
  exact ⟨φ, hφ, by rw [← cancel_epi h.π, reassoc_of% hφ, comp_id]⟩

