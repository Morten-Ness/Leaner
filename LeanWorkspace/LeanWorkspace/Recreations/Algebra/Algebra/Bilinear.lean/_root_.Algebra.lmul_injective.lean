import Mathlib

variable {R A B : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A]

theorem _root_.Algebra.lmul_injective : Function.Injective (Algebra.lmul R A) := fun a₁ a₂ h ↦ by simpa using DFunLike.congr_fun h 1

