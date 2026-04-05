import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

theorem one_kroneckerTMul_one
    [AddCommMonoidWithOne α] [AddCommMonoidWithOne β] [Module R α] [Module R β]
    [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) ⊗ₖₜ[R] (1 : Matrix n n β) = 1 := Matrix.kroneckerMap_one_one _ (zero_tmul _) (tmul_zero _) rfl

unseal mul in

