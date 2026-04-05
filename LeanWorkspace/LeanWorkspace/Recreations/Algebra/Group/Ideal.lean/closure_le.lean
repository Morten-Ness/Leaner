import Mathlib

variable {M : Type*}

variable [Mul M] {s t : Set M} {x : M}

theorem closure_le {I} : closure s ≤ I ↔ s ⊆ I := SubMulAction.closure_le

