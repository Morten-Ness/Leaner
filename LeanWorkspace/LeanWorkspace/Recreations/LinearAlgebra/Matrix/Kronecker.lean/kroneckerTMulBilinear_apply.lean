import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

theorem kroneckerTMulBilinear_apply [Semiring S] [Module S α] [SMulCommClass R S α]
    (A : Matrix l m α) (B : Matrix n p β) :
    Matrix.kroneckerTMulBilinear R S A B = A ⊗ₖₜ[R] B := rfl

