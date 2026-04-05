import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

theorem smul_kroneckerTMul [Monoid S] [DistribMulAction S α] [SMulCommClass R S α]
    (r : S) (A : Matrix l m α) (B : Matrix n p β) :
    (r • A) ⊗ₖₜ[R] B = r • A ⊗ₖₜ[R] B := Matrix.kroneckerMap_smul_left _ _ (fun _ _ => smul_tmul' _ _ _) _ _

