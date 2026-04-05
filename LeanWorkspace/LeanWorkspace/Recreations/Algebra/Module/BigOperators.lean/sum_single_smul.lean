import Mathlib

variable {ι κ α β R M : Type*}

variable [DecidableEq ι] [Fintype ι] [AddCommMonoid α]

theorem sum_single_smul
    {R : Type*} [Semiring R] [Module R α] (f : ι → α) (r : R) (i₀ : ι) :
    ∑ i, (Pi.single (M := fun _ ↦ R) i₀ r i) • f i = r • f i₀ := by
  rw [Finset.sum_eq_single i₀, Pi.single_eq_same] <;> aesop

