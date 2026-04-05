import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

variable {R₁ R₂ R₃ R₁' R₂' R₃' R₁'' R₂'' : Type*} {M₁ M₂ M₃ M₁' M₂' M₃' M₁'' M₂'' : Type*}

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable [CommSemiring R₁'] [CommSemiring R₂'] [CommSemiring R₃']

variable [CommSemiring R₁''] [CommSemiring R₂'']

variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [AddCommMonoid M₁'] [AddCommMonoid M₂'] [AddCommMonoid M₃']

variable [AddCommMonoid M₁''] [AddCommMonoid M₂'']

variable [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]

variable [Module R₁' M₁'] [Module R₂' M₂'] [Module R₃' M₃']

variable [Module R₁'' M₁''] [Module R₂'' M₂'']

variable {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}

variable {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂}

variable {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁}

variable {σ₁'₂' : R₁' →+* R₂'} {σ₂'₁' : R₂' →+* R₁'}

variable {σ₂'₃' : R₂' →+* R₃'} {σ₃'₂' : R₃' →+* R₂'}

variable {σ₁'₃' : R₁' →+* R₃'} {σ₃'₁' : R₃' →+* R₁'}

variable {σ₁''₂'' : R₁'' →+* R₂''} {σ₂''₁'' : R₂'' →+* R₁''}

variable {σ₁₁' : R₁ →+* R₁'} {σ₂₂' : R₂ →+* R₂'} {σ₃₃' : R₃ →+* R₃'}

variable {σ₁'₁'' : R₁' →+* R₁''} {σ₂'₂'' : R₂' →+* R₂''}

variable {σ₁₁'' : R₁ →+* R₁''} {σ₂₂'' : R₂ →+* R₂''}

variable {σ₂₁' : R₂ →+* R₁'} {σ₁₂' : R₁ →+* R₂'}

variable {σ₃₂' : R₃ →+* R₂'} {σ₂₃' : R₂ →+* R₃'}

variable {σ₃₁' : R₃ →+* R₁'} {σ₁₃' : R₁ →+* R₃'}

variable {σ₂'₁'' : R₂' →+* R₁''} {σ₁'₂'' : R₁' →+* R₂''}

variable {σ₂₁'' : R₂ →+* R₁''} {σ₁₂'' : R₁ →+* R₂''}

variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

variable [RingHomInvPair σ₁'₂' σ₂'₁'] [RingHomInvPair σ₂'₁' σ₁'₂']

variable [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]

variable [RingHomInvPair σ₂'₃' σ₃'₂'] [RingHomInvPair σ₃'₂' σ₂'₃']

variable [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]

variable [RingHomInvPair σ₁'₃' σ₃'₁'] [RingHomInvPair σ₃'₁' σ₁'₃']

variable [RingHomInvPair σ₁''₂'' σ₂''₁''] [RingHomInvPair σ₂''₁'' σ₁''₂'']

variable [RingHomCompTriple σ₁₁' σ₁'₁'' σ₁₁''] [RingHomCompTriple σ₂₂' σ₂'₂'' σ₂₂'']

variable [RingHomCompTriple σ₁₁' σ₁'₂' σ₁₂'] [RingHomCompTriple σ₂₁ σ₁₂' σ₂₂']

variable [RingHomCompTriple σ₂₂' σ₂'₁' σ₂₁'] [RingHomCompTriple σ₁₂ σ₂₁' σ₁₁']

variable [RingHomCompTriple σ₁₁' σ₁'₃' σ₁₃'] [RingHomCompTriple σ₃₁ σ₁₃' σ₃₃']

variable [RingHomCompTriple σ₃₃' σ₃'₁' σ₃₁'] [RingHomCompTriple σ₁₃ σ₃₁' σ₁₁']

variable [RingHomCompTriple σ₂₂' σ₂'₃' σ₂₃'] [RingHomCompTriple σ₃₂ σ₂₃' σ₃₃']

variable [RingHomCompTriple σ₃₃' σ₃'₂' σ₃₂'] [RingHomCompTriple σ₂₃ σ₃₂' σ₂₂']

variable [RingHomCompTriple σ₁₁'' σ₁''₂'' σ₁₂''] [RingHomCompTriple σ₂₁ σ₁₂'' σ₂₂'']

variable [RingHomCompTriple σ₂₂'' σ₂''₁'' σ₂₁''] [RingHomCompTriple σ₁₂ σ₂₁'' σ₁₁'']

variable [RingHomCompTriple σ₁'₁'' σ₁''₂'' σ₁'₂''] [RingHomCompTriple σ₂'₁' σ₁'₂'' σ₂'₂'']

variable [RingHomCompTriple σ₂'₂'' σ₂''₁'' σ₂'₁''] [RingHomCompTriple σ₁'₂' σ₂'₁'' σ₁'₁'']

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

variable [RingHomCompTriple σ₁'₂' σ₂'₃' σ₁'₃'] [RingHomCompTriple σ₃'₂' σ₂'₁' σ₃'₁']

theorem conj_apply_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') (x : M₂') :
    e.conj f x = e (f (e.symm x)) := rfl

