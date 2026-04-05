import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [CompleteLattice M] [One M]

variable [Nonempty ι]

theorem iSup_mulIndicator {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f : ι → α → M}
    {s : ι → Set α} (h1 : (⊥ : M) = 1) (hf : Monotone f) (hs : Monotone s) :
    ⨆ i, (s i).mulIndicator (f i) = (⋃ i, s i).mulIndicator (⨆ i, f i) := by
  simp only [le_antisymm_iff, iSup_le_iff]
  refine ⟨fun i ↦ ?_, fun a ↦ ?_⟩
  · grw [← le_iSup f i, ← subset_iUnion s i]
    intro; simp [← h1]
  by_cases ha : a ∈ ⋃ i, s i
  · obtain ⟨i, hi⟩ : ∃ i, a ∈ s i := by simpa using ha
    rw [mulIndicator_of_mem ha, iSup_apply, iSup_apply]
    refine iSup_le fun j ↦ ?_
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine le_iSup_of_le k <| (hf hjk _).trans_eq ?_
    rw [mulIndicator_of_mem (hs hik hi)]
  · rw [mulIndicator_of_notMem ha, ← h1]
    exact bot_le

