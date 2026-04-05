import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [One M]

theorem mulSupport_iSup [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨆ i, f i x) ⊆ ⋃ i, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', mem_iUnion, not_exists, notMem_mulSupport]
  intro x hx
  simp only [hx, ciSup_const]

