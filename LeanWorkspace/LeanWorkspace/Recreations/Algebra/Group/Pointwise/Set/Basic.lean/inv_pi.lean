import Mathlib

variable {F α β γ : Type*}

variable {ι : Type*} {α : ι → Type*} [∀ i, Inv (α i)]

theorem inv_pi (s : Set ι) (t : ∀ i, Set (α i)) : (s.pi t)⁻¹ = s.pi fun i ↦ (t i)⁻¹ := by ext x; simp

