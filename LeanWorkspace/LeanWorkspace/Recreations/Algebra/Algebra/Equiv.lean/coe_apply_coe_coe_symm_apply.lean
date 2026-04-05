import Mathlib

variable {R : Type uR}

variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}

variable {A₁' : Type uA₁'} {A₂' : Type uA₂'} {A₃' : Type uA₃'}

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]

variable [Semiring A₁'] [Semiring A₂'] [Semiring A₃']

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

variable [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']

variable (e : A₁ ≃ₐ[R] A₂)

theorem coe_apply_coe_coe_symm_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
    (f : F) (x : A₂) :
    f ((f : A₁ ≃ₐ[R] A₂).symm x) = x := EquivLike.right_inv f x

