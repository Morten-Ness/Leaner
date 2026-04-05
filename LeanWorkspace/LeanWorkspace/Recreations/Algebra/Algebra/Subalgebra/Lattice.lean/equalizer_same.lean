import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable {F : Type*}

variable [FunLike F A B] [AlgHomClass F R A B]

theorem equalizer_same (φ : F) : equalizer φ φ = ⊤ := AlgHom.equalizer_eq_top.2 rfl

