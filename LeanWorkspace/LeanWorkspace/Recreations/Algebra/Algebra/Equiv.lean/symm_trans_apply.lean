import Mathlib

variable {R : Type uR}

variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}

variable {A₁' : Type uA₁'} {A₂' : Type uA₂'} {A₃' : Type uA₃'}

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]

variable [Semiring A₁'] [Semiring A₂'] [Semiring A₃']

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

variable [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']

variable (e : A₁ ≃ₐ[R] A₂)

theorem symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

