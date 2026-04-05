import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable [Mul N]

theorem eqOn_closure {f g : M →ₙ* N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (Subsemigroup.closure s) := show Subsemigroup.closure s ≤ f.eqLocus g from Subsemigroup.closure_le.2 h

