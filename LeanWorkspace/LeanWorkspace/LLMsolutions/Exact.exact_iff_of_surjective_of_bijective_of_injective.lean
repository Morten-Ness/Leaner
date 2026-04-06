FAIL
import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem exact_iff_of_surjective_of_bijective_of_injective
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    [Module R N₁] [Module R N₂] [Module R N₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R] N₂) (g' : N₂ →ₗ[R] N₃)
    (τ₁ : M₁ →ₗ[R] N₁) (τ₂ : M₂ →ₗ[R] N₂) (τ₃ : M₃ →ₗ[R] N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f) (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂) (h₃ : Function.Injective τ₃) :
    Function.Exact f g ↔ Function.Exact f' g' := by
  rcases h₂ with ⟨h₂inj, h₂surj⟩
  constructor
  · intro hex
    intro y
    constructor
    · intro hy
      rcases h₂surj y with ⟨x, rfl⟩
      have hx : g x = 0 := by
        apply h₃
        rw [← comm₂₃]
        exact hy
      rcases (hex x).mp hx with ⟨z, rfl⟩
      refine ⟨τ₁ z, ?_⟩
      rw [comm₁₂]
    · rintro ⟨x, rfl⟩
      have : g' (f' x) = g' (τ₂ (f x)) := by
        rw [comm₁₂]
      rw [this]
      rw [comm₂₃]
      exact (hex (f x)).mpr ⟨x, rfl⟩
  · intro hex
    intro y
    constructor
    · intro hy
      have hy' : g' (τ₂ y) = 0 := by
        rw [comm₂₃, hy, map_zero]
      rcases (hex (τ₂ y)).mp hy' with ⟨x, hx⟩
      rcases h₁ x with ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      apply h₂inj
      rw [← hx, comm₁₂]
    · rintro ⟨x, rfl⟩
      apply h₃
      rw [comm₂₃, (hex (τ₂ (f x))).mpr ⟨τ₁ x, by rw [comm₁₂]⟩, map_zero]
