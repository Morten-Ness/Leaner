import Mathlib

variable {R R' S M M' : Type*}

variable [Semiring R] [Semiring R']

variable [AddCommMonoid M] [AddCommMonoid M']

variable [Module R M] [Module R' M']

variable {σ₁₂ : R →+* R'}

variable {S' T' : Type*}

variable [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M]

variable [Monoid T'] [DistribMulAction T' M] [SMulCommClass R T' M]

theorem _root_.DomMulAct.coe_smul_linearMap (a : S'ᵈᵐᵃ) (f : M →ₛₗ[σ₁₂] M') :
    (a • f : M →ₛₗ[σ₁₂] M') = a • (f : M → M') := rfl

