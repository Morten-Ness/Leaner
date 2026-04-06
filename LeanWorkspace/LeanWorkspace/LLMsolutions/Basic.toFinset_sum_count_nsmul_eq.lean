import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι]

theorem toFinset_sum_count_nsmul_eq (s : Multiset ι) :
    ∑ a ∈ s.toFinset, s.count a • {a} = s := by
  classical
  ext x
  simp [Multiset.count_sum, Multiset.count_nsmul]
