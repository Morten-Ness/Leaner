FAIL
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

theorem pow_toLinearMap (σ : A₁ ≃ₐ[R] A₁) (n : ℕ) :
    (σ ^ n).toLinearMap = σ.toLinearMap ^ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change (σ.toLinearMap.comp (σ ^ n).toLinearMap) = σ.toLinearMap ^ n * σ.toLinearMap
      rw [ih]
      rfl
