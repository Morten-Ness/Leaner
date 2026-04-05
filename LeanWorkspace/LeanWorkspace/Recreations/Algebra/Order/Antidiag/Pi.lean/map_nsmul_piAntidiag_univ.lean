import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι]

theorem map_nsmul_piAntidiag_univ [Fintype ι] (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (Finset.piAntidiag (univ : Finset ι) m).map
        ⟨(n • ·), fun _ _ h ↦ funext fun i ↦ mul_right_injective₀ hn (congr_fun h i)⟩ =
      {f ∈ Finset.piAntidiag (univ : Finset ι) (n * m) | ∀ i, n ∣ f i} := by
  simpa using Finset.map_nsmul_piAntidiag (univ : Finset ι) m hn

