import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem mulExact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommMonoid M₁] [CommMonoid M₂] [CommMonoid M₃]
    [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]
    (f : M₁ →* M₂) (g : M₂ →* M₃) (f' : N₁ →* N₂) (g' : N₂ →* N₃)
    (τ₁ : M₁ →* N₁) (τ₂ : M₂ →* N₂) (τ₃ : M₃ →* N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f)
    (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    Function.MulExact f g ↔ Function.MulExact f' g' := by
  replace comm₁₂ := DFunLike.congr_fun comm₁₂
  replace comm₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at comm₁₂ comm₂₃
  constructor
  · intro h y₂
    obtain ⟨x₂, rfl⟩ := h₂.2 y₂
    constructor
    · intro hx₂
      obtain ⟨x₁, rfl⟩ := (h x₂).1 (h₃ (by simpa only [map_one, comm₂₃] using hx₂))
      exact ⟨τ₁ x₁, by simp only [comm₁₂]⟩
    · rintro ⟨y₁, hy₁⟩
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      rw [comm₂₃, (h x₂).2 _, map_one]
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
  · intro h x₂
    constructor
    · intro hx₂
      obtain ⟨y₁, hy₁⟩ := (h (τ₂ x₂)).1 (by simp only [comm₂₃, hx₂, map_one])
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
    · rintro ⟨x₁, rfl⟩
      apply h₃
      simp only [← comm₁₂, ← comm₂₃, Function.MulExact.apply_apply_eq_one h (τ₁ x₁), map_one]

