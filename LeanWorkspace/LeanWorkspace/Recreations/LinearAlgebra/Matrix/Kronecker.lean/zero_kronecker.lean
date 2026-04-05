import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem zero_kronecker [MulZeroClass α] (B : Matrix n p α) : (0 : Matrix l m α) ⊗ₖ B = 0 := Matrix.kroneckerMap_zero_left _ zero_mul B

