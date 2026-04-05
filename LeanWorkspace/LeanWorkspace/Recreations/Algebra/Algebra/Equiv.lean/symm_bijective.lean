import Mathlib

variable {R : Type uR}

variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}

variable {A₁' : Type uA₁'} {A₂' : Type uA₂'} {A₃' : Type uA₃'}

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]

variable [Semiring A₁'] [Semiring A₂'] [Semiring A₃']

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

variable [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']

variable (e : A₁ ≃ₐ[R] A₂)

theorem symm_bijective : Function.Bijective (AlgEquiv.symm : (A₁ ≃ₐ[R] A₂) → A₂ ≃ₐ[R] A₁) := Function.bijective_iff_has_inverse.mpr ⟨_, AlgEquiv.symm_symm, AlgEquiv.symm_symm⟩

