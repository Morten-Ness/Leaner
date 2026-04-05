import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

theorem Set.piecewise_mul [∀ i, Mul (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ := s.piecewise_op₂ f₁ _ _ _ fun _ => (· * ·)

