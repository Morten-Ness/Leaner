import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι]

theorem nsmul_piAntidiag_univ [Fintype ι] (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    n •ℕ (Finset.piAntidiag univ m) = {f ∈ Finset.piAntidiag (univ : Finset ι) (n * m) | ∀ i, n ∣ f i} := by
  simpa using Finset.nsmul_piAntidiag (univ : Finset ι) m hn

