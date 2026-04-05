import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_mul_compl_eq_piecewise [DecidablePred (· ∈ s)] (f g : α → M) :
    s.mulIndicator f * sᶜ.mulIndicator g = s.piecewise f g := by
  ext x
  by_cases h : x ∈ s
  · rw [piecewise_eq_of_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_mem h,
      Set.mulIndicator_of_notMem (Set.notMem_compl_iff.2 h), mul_one]
  · rw [piecewise_eq_of_notMem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_notMem h,
      Set.mulIndicator_of_mem (Set.mem_compl h), one_mul]

