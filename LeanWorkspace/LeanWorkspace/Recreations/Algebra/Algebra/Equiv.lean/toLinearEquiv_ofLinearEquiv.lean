import Mathlib

variable {R : Type uR}

variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}

variable {A₁' : Type uA₁'} {A₂' : Type uA₂'} {A₃' : Type uA₃'}

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]

variable [Semiring A₁'] [Semiring A₂'] [Semiring A₃']

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

variable [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']

variable (e : A₁ ≃ₐ[R] A₂)

variable (l : A₁ ≃ₗ[R] A₂) (map_one : l 1 = 1) (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)

theorem toLinearEquiv_ofLinearEquiv : AlgEquiv.toLinearEquiv (AlgEquiv.ofLinearEquiv l map_one map_mul) = l := rfl

