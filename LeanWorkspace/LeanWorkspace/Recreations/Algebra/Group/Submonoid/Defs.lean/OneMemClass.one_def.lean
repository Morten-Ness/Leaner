import Mathlib

variable {M : Type*} {N : Type*}

variable {A M₁ : Type*} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

theorem one_def : (1 : S') = ⟨1, OneMemClass.one_mem S'⟩ := rfl

