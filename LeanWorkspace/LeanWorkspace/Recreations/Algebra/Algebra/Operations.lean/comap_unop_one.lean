import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem comap_unop_one :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (1 : Submodule R A) = 1 := by
  rw [← map_equiv_eq_comap_symm, Submodule.map_op_one]

