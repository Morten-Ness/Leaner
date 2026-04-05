import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

theorem shortExact_of_iso (e : S₁ ≅ S₂) (h : S₁.ShortExact) : S₂.ShortExact where
  exact := exact_of_iso e h.exact
  mono_f := by
    suffices Mono (S₂.f ≫ e.inv.τ₂) by
      exact mono_of_mono _ e.inv.τ₂
    have := h.mono_f
    rw [← e.inv.comm₁₂]
    apply mono_comp
  epi_g := by
    suffices Epi (e.hom.τ₂ ≫ S₂.g) by
      exact epi_of_epi e.hom.τ₂ _
    have := h.epi_g
    rw [e.hom.comm₂₃]
    apply epi_comp

