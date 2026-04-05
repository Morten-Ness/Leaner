import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem mem_iSup {ι : Sort*} (p : ι → Submonoid M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← Submonoid.closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [Submonoid.closure_singleton_le_iff_mem]

