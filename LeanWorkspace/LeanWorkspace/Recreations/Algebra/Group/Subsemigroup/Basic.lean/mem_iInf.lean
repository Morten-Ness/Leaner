import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem mem_iInf {ι : Sort*} {S : ι → Subsemigroup M} {x : M} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, Subsemigroup.mem_sInf, Set.forall_mem_range]

