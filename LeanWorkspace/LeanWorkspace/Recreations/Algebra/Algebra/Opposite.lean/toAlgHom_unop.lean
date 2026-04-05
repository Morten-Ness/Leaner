import Mathlib

variable {R S A B : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]

variable [IsScalarTower R S A]

theorem toAlgHom_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) : f.unop.toAlgHom = AlgHom.unop f.toAlgHom := rfl

