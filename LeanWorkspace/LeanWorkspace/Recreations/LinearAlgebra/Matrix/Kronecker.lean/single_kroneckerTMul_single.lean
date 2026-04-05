import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

theorem single_kroneckerTMul_single
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (i₁ : l) (j₁ : m) (i₂ : n) (j₂ : p) (a : α) (b : β) :
    single i₁ j₁ a ⊗ₖₜ[R] single i₂ j₂ b = single (i₁, i₂) (j₁, j₂) (a ⊗ₜ b) := Matrix.kroneckerMap_single_single _ _ _ _ _ (zero_tmul _) (tmul_zero _) _ _

