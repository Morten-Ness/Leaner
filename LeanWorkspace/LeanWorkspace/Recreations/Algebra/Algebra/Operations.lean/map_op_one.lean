import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem map_op_one :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (1 : Submodule R A) = 1 := by
  ext x
  induction x
  simp

