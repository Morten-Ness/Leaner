import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

variable [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

theorem conjTranspose_kroneckerTMul [StarRing R] [StarAddMonoid α] [StarAddMonoid β]
    [StarModule R α] [StarModule R β] (x : Matrix l m α) (y : Matrix n p β) :
    (x ⊗ₖₜ[R] y)ᴴ = xᴴ ⊗ₖₜ[R] yᴴ := by
  ext; simp

