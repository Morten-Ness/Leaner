import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

theorem kroneckerTMul_smul [Monoid S] [DistribMulAction S α] [DistribMulAction S β]
    [SMul S R] [SMulCommClass R S α] [IsScalarTower S R α] [IsScalarTower S R β]
    (r : S) (A : Matrix l m α) (B : Matrix n p β) :
    A ⊗ₖₜ[R] (r • B) = r • A ⊗ₖₜ[R] B := Matrix.kroneckerMap_smul_right _ _ (fun _ _ => tmul_smul _ _ _) _ _

