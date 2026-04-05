import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R]

variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M₁' i)]
  [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄] [AddCommMonoid M']

variable [∀ i, Module R (M₁ i)] [∀ i, Module R (M₁' i)]
  [Module R M₂] [Module R M₃] [Module R M₄] [Module R M']

theorem smul_compMultilinearMap [Monoid S] [DistribMulAction S M₃] [SMulCommClass R S M₃]
    (g : M₂ →ₗ[R] M₃) (s : S) (f : MultilinearMap R M₁ M₂) :
    (s • g).compMultilinearMap f = s • g.compMultilinearMap f := rfl

