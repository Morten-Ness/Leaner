import Mathlib

variable {M : Type*}

variable [Mul M] {s t : Set M} {x : M}

theorem mem_closure : x ∈ closure s ↔ ∀ p : SemigroupIdeal M, s ⊆ p → x ∈ p := SubMulAction.mem_closure

