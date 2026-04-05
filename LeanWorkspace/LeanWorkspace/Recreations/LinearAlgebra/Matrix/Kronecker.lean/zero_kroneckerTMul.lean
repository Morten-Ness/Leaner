import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

theorem zero_kroneckerTMul (B : Matrix n p β) : (0 : Matrix l m α) ⊗ₖₜ[R] B = 0 := Matrix.kroneckerMap_zero_left _ (zero_tmul α) B

