import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable {F : Type*}

variable [FunLike F A B] [AlgHomClass F R A B]

theorem equalizer_eq_top {φ ψ : F} : equalizer φ ψ = ⊤ ↔ φ = ψ := by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

