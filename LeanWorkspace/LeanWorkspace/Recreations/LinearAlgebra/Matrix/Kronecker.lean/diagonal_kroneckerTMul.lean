import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

theorem diagonal_kroneckerTMul [DecidableEq l] (a : l → α) (B : Matrix m n β) :
    diagonal a ⊗ₖₜ[R] B =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
        (blockDiagonal fun i => B.map fun b => a i ⊗ₜ[R] b) := Matrix.kroneckerMap_diagonal_left _ (zero_tmul _) _ _

-- simp-normal form is `kroneckerTMul_assoc'`

