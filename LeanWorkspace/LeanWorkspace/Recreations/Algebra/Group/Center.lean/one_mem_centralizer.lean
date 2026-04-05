import Mathlib

variable {M : Type*} {S T : Set M}

variable [MulOneClass M]

theorem one_mem_centralizer : (1 : M) ∈ Set.centralizer S := by simp [Set.mem_centralizer_iff]

