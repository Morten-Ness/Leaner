import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem mono_τ₂_of_exact_of_mono {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.Exact) [Mono S₁.f] [Mono S₂.f] [Mono φ.τ₁] [Mono φ.τ₃] : Mono φ.τ₂ := by
  rw [mono_iff_cancel_zero]
  intro A x₂ hx₂
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ ≫ S₁.f = x₂ := ⟨_, CategoryTheory.ShortComplex.Exact.lift_f h₁ x₂
    (by simp only [← cancel_mono φ.τ₃, assoc, zero_comp, ← φ.comm₂₃, reassoc_of% hx₂])⟩
  suffices x₁ = 0 by rw [← hx₁, this, zero_comp]
  simp only [← cancel_mono φ.τ₁, ← cancel_mono S₂.f, assoc, φ.comm₁₂, zero_comp,
    reassoc_of% hx₁, hx₂]

attribute [local instance] balanced_opposite

