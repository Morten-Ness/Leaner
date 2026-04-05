import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [CompleteLattice M] [One M]

theorem mulIndicator_iUnion_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋃ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iUnion] at hx
    refine le_antisymm ?_ (iSup_le fun i ↦ Set.mulIndicator_le_self' (fun x _ ↦ h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_iSup_of_le i (ge_of_eq <| mulIndicator_of_mem hi _)
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iUnion, not_exists] at hx
    simp [hx, ← h1]

