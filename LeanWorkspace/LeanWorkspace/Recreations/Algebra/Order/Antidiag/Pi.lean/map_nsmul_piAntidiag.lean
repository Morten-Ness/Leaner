import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι]

theorem map_nsmul_piAntidiag (s : Finset ι) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (Finset.piAntidiag s m).map
      ⟨(n • ·), fun _ _ h ↦ funext fun i ↦ mul_right_injective₀ hn (congr_fun h i)⟩ =
        {f ∈ Finset.piAntidiag s (n * m) | ∀ i ∈ s, n ∣ f i} := by
  classical rw [map_eq_image]; exact Finset.nsmul_piAntidiag _ _ hn

