import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem mem_iSup {ι : Sort*} (p : ι → Subsemigroup M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← Subsemigroup.closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [Subsemigroup.closure_singleton_le_iff_mem]

