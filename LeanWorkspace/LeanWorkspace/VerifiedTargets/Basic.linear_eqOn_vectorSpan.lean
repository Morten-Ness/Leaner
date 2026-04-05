import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem linear_eqOn_vectorSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ →ᵃ[k] P₂}
    (h_agree : s.EqOn f g) : Set.EqOn f.linear g.linear (vectorSpan k s) := by
  simp only [vectorSpan_def]
  apply LinearMap.eqOn_span
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, h_agree hy]

