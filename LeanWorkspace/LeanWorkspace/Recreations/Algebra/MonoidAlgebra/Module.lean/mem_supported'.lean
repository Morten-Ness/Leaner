import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable {S : Type*}

variable [Semiring R] [Semiring S] [Module R S] {s t : Set M} {x : S[M]}

theorem mem_supported' : x ∈ MonoidAlgebra.supported R S s ↔ ∀ m ∉ s, x.coeff m = 0 := by
  simp [mem_supported, Set.subset_def, not_imp_comm]

