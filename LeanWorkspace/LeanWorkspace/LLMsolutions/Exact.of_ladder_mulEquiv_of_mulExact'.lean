FAIL
import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ →* X₂} {f₂₃ : X₂ →* X₃} {g₁₂ : Y₁ →* Y₂} {g₂₃ : Y₂ →* Y₃}

theorem of_ladder_mulEquiv_of_mulExact' (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) (H : Function.MulExact g₁₂ g₂₃) : Function.MulExact f₁₂ f₂₃ := by
  intro x
  constructor
  · intro hx
    have hx' : g₂₃ (e₂ x) = 1 := by
      calc
        g₂₃ (e₂ x) = e₃ (f₂₃ x) := by
          have h := congrArg (fun h : X₂ →* Y₃ => h x) comm₂₃
          simpa using h
        _ = e₃ 1 := by simpa [hx]
        _ = 1 := map_one e₃
    exact (H (e₂ x)).mp hx'
  · intro hx
    have hx' : g₂₃ (e₂ x) = 1 := by
      have : e₂ x ∈ Set.range g₁₂ := by
        rcases hx with ⟨y, rfl⟩
        refine ⟨e₁ y, ?_⟩
        have h := congrArg (fun h : X₁ →* Y₂ => h y) comm₁₂
        simpa using h
      exact (H (e₂ x)).mpr this
    have hx'' : f₂₃ x = 1 := by
      apply e₃.injective
      calc
        e₃ (f₂₃ x) = g₂₃ (e₂ x) := by
          have h := congrArg (fun h : X₂ →* Y₃ => h x) comm₂₃
          simpa using h.symm
        _ = 1 := hx'
        _ = e₃ 1 := by rw [map_one]
    refine ⟨e₁.symm ((H (e₂ x)).mp hx'), ?_⟩
    rcases (H (e₂ x)).mp hx' with ⟨y, hy⟩
    refine ⟨e₁.symm y, ?_⟩
    apply e₂.injective
    calc
      e₂ (f₁₂ (e₁.symm y)) = g₁₂ (e₁ (e₁.symm y)) := by
        have h := congrArg (fun h : X₁ →* Y₂ => h (e₁.symm y)) comm₁₂
        simpa using h.symm
      _ = g₁₂ y := by simp
      _ = e₂ x := hy
