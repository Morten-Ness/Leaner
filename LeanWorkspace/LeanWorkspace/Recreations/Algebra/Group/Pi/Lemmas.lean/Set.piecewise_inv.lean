import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

theorem Set.piecewise_inv [∀ i, Inv (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ g₁ : ∀ i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ := s.piecewise_op f₁ g₁ fun _ x => x⁻¹

