import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem map_op_mul :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M * N) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) N *
        map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M := by
  apply le_antisymm
  · simp_rw [map_le_iff_le_comap]
    refine Submodule.mul_le.2 fun m hm n hn => ?_
    rw [mem_comap, map_equiv_eq_comap_symm, map_equiv_eq_comap_symm]
    change op n * op m ∈ _
    exact Submodule.mul_mem_mul hn hm
  · refine Submodule.mul_le.2 (MulOpposite.rec' fun m hm => MulOpposite.rec' fun n hn => ?_)
    rw [Submodule.mem_map_equiv] at hm hn ⊢
    exact Submodule.mul_mem_mul hn hm

