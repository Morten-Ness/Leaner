FAIL
import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ →* X₂} {f₂₃ : X₂ →* X₃} {g₁₂ : Y₁ →* Y₂} {g₂₃ : Y₂ →* Y₃}

theorem of_ladder_mulEquiv_of_mulExact (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : Function.MulExact f₁₂ f₂₃) : Function.MulExact g₁₂ g₂₃ := by
  intro y
  constructor
  · rintro ⟨y₁, rfl⟩
    rcases e₁.surjective y₁ with ⟨x₁, rfl⟩
    refine ⟨e₂ (f₁₂ x₁), ?_, ?_⟩
    · exact DFunLike.congr_fun comm₁₂ x₁
    · have h := DFunLike.congr_fun comm₂₃ (f₁₂ x₁)
      rw [H x₁] at h
      simpa using h
  · rintro ⟨y₂, hy₂, hg₂₃y₂⟩
    rcases e₂.surjective y₂ with ⟨x₂, rfl⟩
    have hx₂ : f₂₃ x₂ = 1 := by
      apply e₃.injective
      rw [show g₂₃ (e₂ x₂) = e₃ (f₂₃ x₂) from DFunLike.congr_fun comm₂₃ x₂]
      simpa using hg₂₃y₂
    rcases (H x₂).mp hx₂ with ⟨x₁, rfl⟩
    refine ⟨e₁ x₁, ?_⟩
    exact DFunLike.congr_fun comm₁₂ x₁
