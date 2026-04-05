import Mathlib

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

theorem piecewise_smul [∀ i, SMul M (α i)] (s : Set ι) [∀ i, Decidable (i ∈ s)]
    (c : M) (f₁ g₁ : ∀ i, α i) : s.piecewise (c • f₁) (c • g₁) = c • s.piecewise f₁ g₁ := s.piecewise_op (δ' := α) f₁ _ fun _ ↦ (c • ·)

