import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem exists_inv_mem {p : α → Prop} : (∃ x, x⁻¹ ∈ s ∧ p x) ↔ ∃ x ∈ s, p x⁻¹ := by
  constructor
  · rintro ⟨x, hx, hp⟩
    refine ⟨x⁻¹, ?_, ?_⟩
    · simpa using hx
    · simpa using hp
  · rintro ⟨x, hx, hp⟩
    refine ⟨x⁻¹, ?_, ?_⟩
    · simpa using hx
    · simpa using hp
