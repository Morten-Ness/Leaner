import Mathlib

variable {M : Type*}

variable [Mul M] {s t : Set M} {x : M}

theorem subset_closure : s ⊆ closure s := SubMulAction.subset_closure

