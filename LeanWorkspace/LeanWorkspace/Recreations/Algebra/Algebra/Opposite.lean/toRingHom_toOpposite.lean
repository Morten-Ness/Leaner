import Mathlib

variable {R S A B : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]

variable [IsScalarTower R S A]

theorem toRingHom_toOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) :
    (f.toOpposite hf : A →+* Bᵐᵒᵖ) = (f : A →+* B).toOpposite hf := rfl

