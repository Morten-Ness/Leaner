import Mathlib

open scoped Pointwise Ring

variable {𝕜 : Type u} {A : Type v}

variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem nonzero_mul_comm (a b : A) : σ (a * b) \ {0} = σ (b * a) \ {0} := by
  suffices h : ∀ x y : A, σ (x * y) \ {0} ⊆ σ (y * x) \ {0} from
    Set.eq_of_subset_of_subset (h a b) (h b a)
  rintro _ _ k ⟨k_mem, k_ne⟩
  change ((Units.mk0 k k_ne) : 𝕜) ∈ _ at k_mem
  exact ⟨spectrum.unit_mem_mul_comm.mp k_mem, k_ne⟩

