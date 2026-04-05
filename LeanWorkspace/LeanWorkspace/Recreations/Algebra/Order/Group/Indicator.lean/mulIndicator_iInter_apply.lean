import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [CompleteLattice M] [One M]

variable [Nonempty ι]

theorem mulIndicator_iInter_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋂ i, s i) f x = ⨅ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋂ i, s i
  · simp_all
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iInter, not_forall] at hx
    rcases hx with ⟨j, hj⟩
    refine le_antisymm (by simp only [← h1, le_iInf_iff, bot_le, forall_const]) ?_
    simpa [mulIndicator_of_notMem hj] using (iInf_le (fun i ↦ (s i).mulIndicator f) j) x

