import Mathlib

open scoped Pointwise Ring

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

variable [FunLike F A B] [AlgHomClass F R A B]

theorem spectrum_apply_subset (φ : F) (a : A) : σ ((φ : A → B) a) ⊆ σ a := fun _ =>
  mt (AlgHom.mem_resolventSet_apply φ)

