import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem iSup_eq_closure {ι : Sort*} (p : ι → Subsemigroup M) :
    ⨆ i, p i = Subsemigroup.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Subsemigroup.closure_iUnion, Subsemigroup.closure_eq]

