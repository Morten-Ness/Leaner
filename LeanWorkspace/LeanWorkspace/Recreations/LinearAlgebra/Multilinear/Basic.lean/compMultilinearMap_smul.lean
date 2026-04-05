import Mathlib
universe uR uS uι v v' v₁ v₁' v₁'' v₂ v₃ v₄

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R]

variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M₁' i)]
  [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄] [AddCommMonoid M']

variable [∀ i, Module R (M₁ i)] [∀ i, Module R (M₁' i)]
  [Module R M₂] [Module R M₃] [Module R M₄] [Module R M']

theorem compMultilinearMap_smul [DistribSMul S M₂] [DistribSMul S M₃]
    [SMulCommClass R S M₂] [SMulCommClass R S M₃] [CompatibleSMul M₂ M₃ S R]
    (g : M₂ →ₗ[R] M₃) (s : S) (f : MultilinearMap R M₁ M₂) :
    g.compMultilinearMap (s • f) = s • g.compMultilinearMap f := MultilinearMap.ext fun _ => g.map_smul_of_tower _ _
