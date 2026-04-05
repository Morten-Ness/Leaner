import Mathlib

variable {R A B : Type*}

variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]

variable [SMulCommClass R A A] [IsScalarTower R A A]

variable [SMulCommClass R B B] [IsScalarTower R B B]

theorem map_mul_iff (f : A →ₗ[R] B) :
    (∀ x y, f (x * y) = f x * f y) ↔
      (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B ∘ₗ f).compl₂ f := Iff.symm LinearMap.ext_iff₂

