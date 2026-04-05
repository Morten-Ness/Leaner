import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

variable [∀ i, AddCommMonoid (M₁' i)] [∀ i, Module R (M₁' i)]

variable [∀ i, AddCommMonoid (M₁'' i)] [∀ i, Module R (M₁'' i)]

theorem compLinearMap_assoc (g : MultilinearMap R M₁'' M₂) (f₁ : ∀ i, M₁' i →ₗ[R] M₁'' i)
    (f₂ : ∀ i, M₁ i →ₗ[R] M₁' i) :
    (g.compLinearMap f₁).compLinearMap f₂ = g.compLinearMap fun i => f₁ i ∘ₗ f₂ i := rfl

