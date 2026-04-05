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
    Function.Exact f g ↔ Function.Exact f' g' := AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    f.toAddMonoidHom g.toAddMonoidHom f'.toAddMonoidHom g'.toAddMonoidHom
    τ₁.toAddMonoidHom τ₂.toAddMonoidHom τ₃.toAddMonoidHom
    (by ext; apply DFunLike.congr_fun comm₁₂) (by ext; apply DFunLike.congr_fun comm₂₃) h₁ h₂ h₃

