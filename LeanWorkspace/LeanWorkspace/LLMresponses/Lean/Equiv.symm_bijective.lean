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

theorem symm_bijective : Function.Bijective (AlgEquiv.symm : (A₁ ≃ₐ[R] A₂) → A₂ ≃ₐ[R] A₁) := by
  constructor
  · intro f g h
    have := congrArg AlgEquiv.symm h
    simpa using this
  · intro f
    refine ⟨f.symm, ?_⟩
    rfl
