import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x⁻¹, ?_⟩
    simpa using hx
  · rintro ⟨x, hx⟩
    refine ⟨x⁻¹, ?_⟩
    simpa using hx
