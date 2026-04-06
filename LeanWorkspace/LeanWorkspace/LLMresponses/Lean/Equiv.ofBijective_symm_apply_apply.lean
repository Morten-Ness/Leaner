import Mathlib

universe uR uA₁ uA₂ uA₃ uA₁' uA₂' uA₃'

variable {R : Type uR}

variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}

variable {A₁' : Type uA₁'} {A₂' : Type uA₂'} {A₃' : Type uA₃'}

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]

variable [Semiring A₁'] [Semiring A₂'] [Semiring A₃']

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

variable [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']

variable (e : A₁ ≃ₐ[R] A₂)

theorem ofBijective_symm_apply_apply (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) (x : A₁) :
    (AlgEquiv.ofBijective f hf).symm (f x) = x := by
  exact (AlgEquiv.ofBijective f hf).left_inv x
