import Mathlib

variable {M : Type*}

variable [Mul M] {s t : Set M} {x : M}

theorem closure_mono (h : s ⊆ t) : closure s ≤ closure t := SubMulAction.closure_mono h

