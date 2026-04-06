FAIL
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
  rcases h₂ with ⟨h₂inj, h₂surj⟩
  constructor
  · intro h
    intro y
    constructor
    · intro hy
      rcases h₂surj y with ⟨x, rfl⟩
      have hx : g x = 1 := by
        apply h₃
        have hcomm := congrArg (fun k : M₂ →* N₃ => k x) comm₂₃
        simpa [MonoidHom.comp_apply, hy] using hcomm
      rcases (h x).1 hx with ⟨z, rfl⟩
      rcases h₁ z with ⟨w, rfl⟩
      refine ⟨τ₁ w, ?_⟩
      have hcomm := congrArg (fun k : M₁ →* N₂ => k w) comm₁₂
      simpa [MonoidHom.comp_apply] using hcomm
    · rintro ⟨x, rfl⟩
      have hcomm := congrArg (fun k : M₂ →* N₃ => k (f x)) comm₂₃
      apply h₃
      simpa [MonoidHom.comp_apply] using hcomm
  · intro h
    intro x
    constructor
    · intro hx
      have hτ : f' (τ₁ x) ∈ Set.range f' := by
        apply (h (τ₂ x)).mp
        apply h₂inj
        have hcomm := congrArg (fun k : M₂ →* N₃ => k x) comm₂₃
        simpa [MonoidHom.comp_apply, hx] using hcomm
      rcases hτ with ⟨y, hy⟩
      rcases h₂surj y with ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      apply h₂inj
      rw [← hy]
      have hcomm := congrArg (fun k : M₁ →* N₂ => k z) comm₁₂
      simpa [MonoidHom.comp_apply] using hcomm
    · rintro ⟨y, rfl⟩
      apply h₂inj
      have hcomm := congrArg (fun k : M₂ →* N₃ => k (f y)) comm₂₃
      simpa [MonoidHom.comp_apply] using hcomm
