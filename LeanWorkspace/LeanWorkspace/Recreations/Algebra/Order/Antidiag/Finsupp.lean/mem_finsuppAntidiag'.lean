import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

theorem mem_finsuppAntidiag' :
    f ∈ Finset.finsuppAntidiag s n ↔ f.sum (fun _ x ↦ x) = n ∧ f.support ⊆ s := by
  simp only [mem_finsuppAntidiag, and_congr_left_iff]
  rintro hf
  rw [sum_of_support_subset (N := μ) f hf (fun _ x ↦ x) fun _ _ ↦ rfl]

