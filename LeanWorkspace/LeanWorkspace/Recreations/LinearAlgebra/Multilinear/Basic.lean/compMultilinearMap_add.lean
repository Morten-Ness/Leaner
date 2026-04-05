import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R]

variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M₁' i)]
  [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄] [AddCommMonoid M']

variable [∀ i, Module R (M₁ i)] [∀ i, Module R (M₁' i)]
  [Module R M₂] [Module R M₃] [Module R M₄] [Module R M']

theorem compMultilinearMap_add (g : M₂ →ₗ[R] M₃) (f₁ f₂ : MultilinearMap R M₁ M₂) :
    g.compMultilinearMap (f₁ + f₂) = g.compMultilinearMap f₁ + g.compMultilinearMap f₂ := MultilinearMap.ext fun _ => map_add g _ _

