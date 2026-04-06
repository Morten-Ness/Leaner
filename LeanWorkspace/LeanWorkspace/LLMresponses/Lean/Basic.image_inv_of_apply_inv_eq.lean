FAIL
import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem image_inv_of_apply_inv_eq {f g : α → β} (H : ∀ x ∈ s, f x⁻¹ = g x) :
    f '' (s⁻¹) = g '' s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x⁻¹, ?_, ?_⟩
    · simpa [Set.mem_inv] using hx
    · exact (H (x⁻¹) (by simpa [Set.mem_inv] using hx)).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x⁻¹, ?_, ?_⟩
    · simpa [Set.mem_inv] using hx
    · exact H x hx
