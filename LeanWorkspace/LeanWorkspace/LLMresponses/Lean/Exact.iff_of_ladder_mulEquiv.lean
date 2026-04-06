FAIL
import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ →* X₂} {f₂₃ : X₂ →* X₃} {g₁₂ : Y₁ →* Y₂} {g₂₃ : Y₂ →* Y₃}

theorem iff_of_ladder_mulEquiv (comm₁₂ : g₁₂.comp e₁ = MonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = MonoidHom.comp e₃ f₂₃) : Function.MulExact g₁₂ g₂₃ ↔ Function.MulExact f₁₂ f₂₃ := by
  constructor
  · intro h
    intro x
    constructor
    · intro hx
      have hx' : g₂₃ (e₂ x) = 1 := by
        have hEq := congrArg (fun k : X₂ →* Y₃ => k x) comm₂₃
        dsimp at hEq
        rw [hEq, hx, map_one]
      rcases (h (e₂ x)).1 hx' with ⟨y, hy⟩
      refine ⟨e₁.symm y, ?_⟩
      have hEq := congrArg (fun k : X₁ →* Y₂ => k (e₁.symm y)) comm₁₂
      dsimp at hEq
      apply e₂.injective
      rw [← hEq]
      simpa [hy]
    · rintro ⟨x₁, rfl⟩
      have hy : e₂ (f₁₂ x₁) ∈ Set.range g₁₂ := ⟨e₁ x₁, by
        have hEq := congrArg (fun k : X₁ →* Y₂ => k x₁) comm₁₂
        dsimp at hEq
        simpa using hEq.symm⟩
      have hg : g₂₃ (e₂ (f₁₂ x₁)) = 1 := (h (e₂ (f₁₂ x₁))).2 hy
      have hEq := congrArg (fun k : X₂ →* Y₃ => k (f₁₂ x₁)) comm₂₃
      dsimp at hEq
      apply e₃.injective
      rw [hEq, hg, map_one]
  · intro h
    intro y
    constructor
    · intro hy
      have hy' : f₂₃ (e₂.symm y) = 1 := by
        have hEq := congrArg (fun k : X₂ →* Y₃ => k (e₂.symm y)) comm₂₃
        dsimp at hEq
        apply e₃.injective
        rw [hEq, hy, map_one]
      rcases (h (e₂.symm y)).1 hy' with ⟨x, hx⟩
      refine ⟨e₁ x, ?_⟩
      have hEq := congrArg (fun k : X₁ →* Y₂ => k x) comm₁₂
      dsimp at hEq
      rw [hEq, hx]
      simp
    · rintro ⟨y₁, rfl⟩
      have hx : f₁₂ (e₁.symm y₁) ∈ Set.range f₁₂ := ⟨e₁.symm y₁, rfl⟩
      have hf : f₂₃ (f₁₂ (e₁.symm y₁)) = 1 := (h (f₁₂ (e₁.symm y₁))).2 hx
      have hEq1 := congrArg (fun k : X₁ →* Y₂ => k (e₁.symm y₁)) comm₁₂
      dsimp at hEq1
      have hEq2 := congrArg (fun k : X₂ →* Y₃ => k (f₁₂ (e₁.symm y₁))) comm₂₃
      dsimp at hEq2
      rw [← hEq1, ← hEq2, hf]
      simp
