import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

theorem diagonal_kroneckerTMul_diagonal [DecidableEq m] [DecidableEq n] (a : m → α) (b : n → β) :
    diagonal a ⊗ₖₜ[R] diagonal b = diagonal fun mn => a mn.1 ⊗ₜ b mn.2 := Matrix.kroneckerMap_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _

